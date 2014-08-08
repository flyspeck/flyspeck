open Hol_core
open Card
open Products
open Permutations
open Floor
open Vectors
open Determinants
include Topology3

(* ------------------------------------------------------------------------- *)
(* Closed-graph characterization of continuity.                              *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_CLOSED_GRAPH_GEN = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t
        ==> closed_in (subtopology euclidean (s PCROSS t))
                      {pastecart x (f x) | x IN s}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{pastecart (x:real^M) (f x:real^N) | x IN s} =
    {z | z IN s PCROSS t /\ f(fstcart z) - sndcart z IN {vec 0}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_THM; IN_SING;
                PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
                PASTECART_INJ; VECTOR_SUB_EQ] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
    REWRITE_TAC[CLOSED_SING] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    SIMP_TAC[GSYM o_DEF; LINEAR_CONTINUOUS_ON; LINEAR_SNDCART] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; IMAGE_FSTCART_PCROSS] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_EMPTY]]);;

let CONTINUOUS_CLOSED_GRAPH_EQ = prove
 (`!f:real^M->real^N s t.
        compact t /\ IMAGE f s SUBSET t
        ==> (f continuous_on s <=>
             closed_in (subtopology euclidean (s PCROSS t))
                       {pastecart x (f x) | x IN s})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[CONTINUOUS_CLOSED_GRAPH_GEN] THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
   REWRITE_TAC[MATCH_MP CONTINUOUS_ON_CLOSED_GEN th]) THEN
  X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN s /\ (f:real^M->real^N) x IN c} =
    IMAGE fstcart ({pastecart x (f x) | x IN s} INTER
                   (s PCROSS c))`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PASTECART;
                FSTCART_PASTECART; IN_INTER; IN_ELIM_PASTECART_THM;
                PASTECART_IN_PCROSS; PASTECART_INJ] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC CLOSED_MAP_FSTCART THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSED_IN_INTER THEN
    ASM_REWRITE_TAC[] THEN  MATCH_MP_TAC CLOSED_IN_PCROSS THEN
    ASM_REWRITE_TAC[CLOSED_IN_REFL]]);;

let CONTINUOUS_CLOSED_GRAPH = prove
 (`!f:real^M->real^N s.
        closed s /\ f continuous_on s ==> closed {pastecart x (f x) | x IN s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
  EXISTS_TAC `(s:real^M->bool) PCROSS (:real^N)` THEN
  ASM_SIMP_TAC[CLOSED_PCROSS; CLOSED_UNIV] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_GRAPH_GEN THEN
  ASM_REWRITE_TAC[SUBSET_UNIV]);;

let CONTINUOUS_FROM_CLOSED_GRAPH = prove
 (`!f:real^M->real^N s t.
        compact t /\ IMAGE f s SUBSET t /\
        closed {pastecart x (f x) | x IN s}
        ==> f continuous_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP CONTINUOUS_CLOSED_GRAPH_EQ) THEN
  MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; PASTECART_IN_PCROSS] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A cute way of denoting open and closed intervals using overloading.       *)
(* ------------------------------------------------------------------------- *)

let open_interval = new_definition
  `open_interval(a:real^N,b:real^N) =
        {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                        ==> a$i < x$i /\ x$i < b$i}`;;

let closed_interval = new_definition
  `closed_interval(l:(real^N#real^N)list) =
         {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                         ==> FST(HD l)$i <= x$i /\ x$i <= SND(HD l)$i}`;;

make_overloadable "interval" `:A`;;

overload_interface("interval",`open_interval`);;
overload_interface("interval",`closed_interval`);;

let interval = prove
 (`(interval (a,b) = {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                     ==> a$i < x$i /\ x$i < b$i}) /\
   (interval [a,b] = {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                     ==> a$i <= x$i /\ x$i <= b$i})`,
  REWRITE_TAC[open_interval; closed_interval; HD; FST; SND]);;

let IN_INTERVAL = prove
 (`(!x:real^N.
        x IN interval (a,b) <=>
                !i. 1 <= i /\ i <= dimindex(:N)
                    ==> a$i < x$i /\ x$i < b$i) /\
   (!x:real^N.
        x IN interval [a,b] <=>
                !i. 1 <= i /\ i <= dimindex(:N)
                    ==> a$i <= x$i /\ x$i <= b$i)`,
  REWRITE_TAC[interval; IN_ELIM_THM]);;

let IN_INTERVAL_REFLECT = prove
 (`(!a b x. (--x) IN interval[--b,--a] <=> x IN interval[a,b]) /\
   (!a b x. (--x) IN interval(--b,--a) <=> x IN interval(a,b))`,
  SIMP_TAC[IN_INTERVAL; REAL_LT_NEG2; REAL_LE_NEG2; VECTOR_NEG_COMPONENT] THEN
  MESON_TAC[]);;

let REFLECT_INTERVAL = prove
 (`(!a b:real^N. IMAGE (--) (interval[a,b]) = interval[--b,--a]) /\
   (!a b:real^N. IMAGE (--) (interval(a,b)) = interval(--b,--a))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_INTERVAL_REFLECT] THEN MESON_TAC[VECTOR_NEG_NEG]);;

let INTERVAL_EQ_EMPTY = prove
 (`((interval [a:real^N,b] = {}) <=>
    ?i. 1 <= i /\ i <= dimindex(:N) /\ b$i < a$i) /\
   ((interval (a:real^N,b) = {}) <=>
    ?i. 1 <= i /\ i <= dimindex(:N) /\ b$i <= a$i)`,
  REWRITE_TAC[EXTENSION; IN_INTERVAL; NOT_IN_EMPTY] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; GSYM CONJ_ASSOC] THEN
  CONJ_TAC THEN EQ_TAC THENL
   [MESON_TAC[REAL_LE_REFL; REAL_NOT_LE];
    MESON_TAC[REAL_LE_TRANS; REAL_NOT_LE];
    ALL_TAC;
    MESON_TAC[REAL_LT_TRANS; REAL_NOT_LT]] THEN
  SUBGOAL_THEN `!a b. ?c. a < b ==> a < c /\ c < b`
  (MP_TAC o REWRITE_RULE[SKOLEM_THM]) THENL
   [MESON_TAC[REAL_LT_BETWEEN]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `mid:real->real->real`) THEN
  DISCH_THEN(MP_TAC o SPEC
   `(lambda i. mid ((a:real^N)$i) ((b:real^N)$i)):real^N`) THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a /\ b ==> ~c)`] THEN
  SIMP_TAC[LAMBDA_BETA] THEN ASM_MESON_TAC[REAL_NOT_LT]);;

let INTERVAL_NE_EMPTY = prove
 (`(~(interval [a:real^N,b] = {}) <=>
    !i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i) /\
   (~(interval (a:real^N,b) = {}) <=>
    !i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i)`,
  REWRITE_TAC[INTERVAL_EQ_EMPTY] THEN MESON_TAC[REAL_NOT_LE]);;

let SUBSET_INTERVAL_IMP = prove
 (`((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)
    ==> interval[c,d] SUBSET interval[a:real^N,b]) /\
   ((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < c$i /\ d$i < b$i)
    ==> interval[c,d] SUBSET interval(a:real^N,b)) /\
   ((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)
    ==> interval(c,d) SUBSET interval[a:real^N,b]) /\
   ((!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)
    ==> interval(c,d) SUBSET interval(a:real^N,b))`,
  REWRITE_TAC[SUBSET; IN_INTERVAL] THEN REPEAT CONJ_TAC THEN
  DISCH_TAC THEN GEN_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let INTERVAL_SING = prove
 (`interval[a,a] = {a} /\ interval(a,a) = {}`,
  REWRITE_TAC[EXTENSION; IN_SING; NOT_IN_EMPTY; IN_INTERVAL] THEN
  REWRITE_TAC[REAL_LE_ANTISYM; REAL_LT_ANTISYM; CART_EQ; EQ_SYM_EQ] THEN
  MESON_TAC[DIMINDEX_GE_1; LE_REFL]);;

let SUBSET_INTERVAL = prove
 (`(interval[c,d] SUBSET interval[a:real^N,b] <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i <= d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)) /\
   (interval[c,d] SUBSET interval(a:real^N,b) <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i <= d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < c$i /\ d$i < b$i)) /\
   (interval(c,d) SUBSET interval[a:real^N,b] <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i < d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i)) /\
   (interval(c,d) SUBSET interval(a:real^N,b) <=>
        (!i. 1 <= i /\ i <= dimindex(:N) ==> c$i < d$i)
        ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= c$i /\ d$i <= b$i))`,
  let lemma = prove
   (`(!x:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> Q i (x$i))
                 ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> R i (x$i)))
     ==> (!i. 1 <= i /\ i <= dimindex(:N) ==> ?y. Q i y)
         ==> !i y. 1 <= i /\ i <= dimindex(:N) /\ Q i y ==> R i y`,
    DISCH_TAC THEN REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:num->real` STRIP_ASSUME_TAC) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
     SPEC `(lambda j. if j = i then y else f j):real^N`) THEN
    SIMP_TAC[LAMBDA_BETA] THEN ASM_MESON_TAC[]) in
  REPEAT STRIP_TAC THEN
  (MATCH_MP_TAC(TAUT
    `(~q ==> p) /\ (q ==> (p <=> r)) ==> (p <=> q ==> r)`) THEN
   CONJ_TAC THENL
    [DISCH_TAC THEN MATCH_MP_TAC(SET_RULE `s = {} ==> s SUBSET t`) THEN
     REWRITE_TAC[INTERVAL_EQ_EMPTY] THEN ASM_MESON_TAC[REAL_NOT_LT];
     ALL_TAC] THEN
   DISCH_TAC THEN EQ_TAC THEN REWRITE_TAC[SUBSET_INTERVAL_IMP] THEN
   REWRITE_TAC[SUBSET; IN_INTERVAL] THEN
   DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN ANTS_TAC THENL
    [ASM_MESON_TAC[REAL_LT_BETWEEN; REAL_LE_BETWEEN]; ALL_TAC] THEN
   MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
   DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
   ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC)
  THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL];
    ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL];
    ALL_TAC; ALL_TAC] THEN
  (REPEAT STRIP_TAC THENL
    [FIRST_X_ASSUM(MP_TAC o SPEC
      `((c:real^N)$i + min ((a:real^N)$i) ((d:real^N)$i)) / &2`) THEN
     POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
     FIRST_X_ASSUM(MP_TAC o SPEC
      `(max ((b:real^N)$i) ((c:real^N)$i) + (d:real^N)$i) / &2`) THEN
     POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]));;

let DISJOINT_INTERVAL = prove
 (`!a b c d:real^N.
        (interval[a,b] INTER interval[c,d] = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i < a$i \/ d$i < c$i \/ b$i < c$i \/ d$i < a$i)) /\
        (interval[a,b] INTER interval(c,d) = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i < a$i \/ d$i <= c$i \/ b$i <= c$i \/ d$i <= a$i)) /\
        (interval(a,b) INTER interval[c,d] = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i <= a$i \/ d$i < c$i \/ b$i <= c$i \/ d$i <= a$i)) /\
        (interval(a,b) INTER interval(c,d) = {} <=>
          ?i. 1 <= i /\ i <= dimindex(:N) /\
              (b$i <= a$i \/ d$i <= c$i \/ b$i <= c$i \/ d$i <= a$i))`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_INTERVAL; NOT_IN_EMPTY] THEN
  REWRITE_TAC[AND_FORALL_THM; NOT_FORALL_THM] THEN
  REWRITE_TAC[TAUT `~((p ==> q) /\ (p ==> r)) <=> p /\ (~q \/ ~r)`] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  (EQ_TAC THENL
    [DISCH_THEN(MP_TAC o SPEC
      `(lambda i. (max ((a:real^N)$i) ((c:real^N)$i) +
                   min ((b:real^N)$i) ((d:real^N)$i)) / &2):real^N`) THEN
     MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
     DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
     ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
     DISCH_THEN(fun th -> GEN_TAC THEN MP_TAC th) THEN
     MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN SIMP_TAC[] THEN
     REAL_ARITH_TAC]));;

let ENDS_IN_INTERVAL = prove
 (`(!a b. a IN interval[a,b] <=> ~(interval[a,b] = {})) /\
   (!a b. b IN interval[a,b] <=> ~(interval[a,b] = {})) /\
   (!a b. ~(a IN interval(a,b))) /\
   (!a b. ~(b IN interval(a,b)))`,
  REWRITE_TAC[IN_INTERVAL; INTERVAL_NE_EMPTY] THEN
  REWRITE_TAC[REAL_LE_REFL; REAL_LT_REFL] THEN
  MESON_TAC[DIMINDEX_GE_1; LE_REFL]);;

let ENDS_IN_UNIT_INTERVAL = prove
 (`vec 0 IN interval[vec 0,vec 1] /\
   vec 1 IN interval[vec 0,vec 1] /\
   ~(vec 0 IN interval(vec 0,vec 1)) /\
   ~(vec 1 IN interval(vec 0,vec 1))`,
  REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY; VEC_COMPONENT] THEN
  REWRITE_TAC[REAL_POS]);;

let INTER_INTERVAL = prove
 (`interval[a,b] INTER interval[c,d] =
        interval[(lambda i. max (a$i) (c$i)),(lambda i. min (b$i) (d$i))]`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_INTERVAL] THEN
  SIMP_TAC[LAMBDA_BETA; REAL_MAX_LE; REAL_LE_MIN] THEN MESON_TAC[]);;

let INTERVAL_OPEN_SUBSET_CLOSED = prove
 (`!a b. interval(a,b) SUBSET interval[a,b]`,
  REWRITE_TAC[SUBSET; IN_INTERVAL] THEN MESON_TAC[REAL_LT_IMP_LE]);;

let OPEN_INTERVAL_LEMMA = prove
 (`!a b x. a < x /\ x < b
           ==> ?d. &0 < d /\ !x'. abs(x' - x) < d ==> a < x' /\ x' < b`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `min (x - a) (b - x)` THEN REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_REAL_ARITH_TAC);;

let OPEN_INTERVAL = prove
 (`!a:real^N b. open(interval (a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[open_def; interval; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= dimindex(:N)
                    ==> ?d. &0 < d /\
                            !x'. abs(x' - (x:real^N)$i) < d
                                 ==> (a:real^N)$i < x' /\ x' < (b:real^N)$i`
  MP_TAC THENL [ASM_SIMP_TAC[OPEN_INTERVAL_LEMMA]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `inf (IMAGE d (1..dimindex(:N)))` THEN
  SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; FINITE_NUMSEG;
           IMAGE_EQ_EMPTY; NOT_INSERT_EMPTY; NUMSEG_EMPTY;
           ARITH_RULE `n < 1 <=> (n = 0)`; DIMINDEX_NONZERO] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG; dist] THEN
  ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LET_TRANS; VECTOR_SUB_COMPONENT]);;

let CLOSED_INTERVAL = prove
 (`!a:real^N b. closed(interval [a,b])`,
  REWRITE_TAC[CLOSED_LIMPT; LIMPT_APPROACHABLE; IN_INTERVAL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(a:real^N)$i - (x:real^N)$i`);
    FIRST_X_ASSUM(MP_TAC o SPEC `(x:real^N)$i - (b:real^N)$i`)] THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[dist; REAL_NOT_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((z - x :real^N)$i)` THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_ARITH `x < a /\ a <= z ==> a - x <= abs(z - x)`;
               REAL_ARITH `z <= b /\ b < x ==> x - b <= abs(z - x)`]);;

let INTERIOR_CLOSED_INTERVAL = prove
 (`!a:real^N b. interior(interval [a,b]) = interval (a,b)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC INTERIOR_MAXIMAL THEN
    REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED; OPEN_INTERVAL]] THEN
  REWRITE_TAC[interior; SUBSET; IN_INTERVAL; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LT_LE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THENL
   [(let t = `x - (e / &2) % basis i :real^N` in
     DISCH_THEN(MP_TAC o SPEC t) THEN FIRST_X_ASSUM(MP_TAC o SPEC t));
    (let t = `x + (e / &2) % basis i :real^N` in
     DISCH_THEN(MP_TAC o SPEC t) THEN FIRST_X_ASSUM(MP_TAC o SPEC t))] THEN
  REWRITE_TAC[dist; VECTOR_ADD_SUB; VECTOR_ARITH `x - y - x = --y:real^N`] THEN
  ASM_SIMP_TAC[NORM_MUL; NORM_BASIS; NORM_NEG; REAL_MUL_RID;
               REAL_ARITH `&0 < e ==> abs(e / &2) < e`] THEN
  MATCH_MP_TAC(TAUT `~b ==> (a ==> b) ==> ~a`) THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `i:num` THEN
  ASM_SIMP_TAC[DE_MORGAN_THM; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT] THENL
   [DISJ1_TAC THEN REWRITE_TAC[REAL_ARITH `a <= a - b <=> ~(&0 < b)`];
    DISJ2_TAC THEN REWRITE_TAC[REAL_ARITH `a + b <= a <=> ~(&0 < b)`]] THEN
  ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; basis; LAMBDA_BETA; REAL_MUL_RID] THEN
  ASM_REWRITE_TAC[REAL_HALF]);;

let INTERIOR_INTERVAL = prove
 (`(!a b. interior(interval[a,b]) = interval(a,b)) /\
   (!a b. interior(interval(a,b)) = interval(a,b))`,
  SIMP_TAC[INTERIOR_CLOSED_INTERVAL; INTERIOR_OPEN; OPEN_INTERVAL]);;

let BOUNDED_CLOSED_INTERVAL = prove
 (`!a b:real^N. bounded (interval [a,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[bounded; interval] THEN
  EXISTS_TAC `sum(1..dimindex(:N))
                 (\i. abs((a:real^N)$i) + abs((b:real^N)$i))` THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..dimindex(:N)) (\i. abs((x:real^N)$i))` THEN
  REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_LE THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_ARITH
   `a <= x /\ x <= b ==> abs(x) <= abs(a) + abs(b)`]);;

let BOUNDED_INTERVAL = prove
 (`(!a b. bounded (interval [a,b])) /\ (!a b. bounded (interval (a,b)))`,
  MESON_TAC[BOUNDED_CLOSED_INTERVAL; BOUNDED_SUBSET;
            INTERVAL_OPEN_SUBSET_CLOSED]);;

let NOT_INTERVAL_UNIV = prove
 (`(!a b. ~(interval[a,b] = UNIV)) /\
   (!a b. ~(interval(a,b) = UNIV))`,
  MESON_TAC[BOUNDED_INTERVAL; NOT_BOUNDED_UNIV]);;

let COMPACT_INTERVAL = prove
 (`!a b. compact (interval [a,b])`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_INTERVAL; CLOSED_INTERVAL]);;

let OPEN_INTERVAL_MIDPOINT = prove
 (`!a b:real^N.
        ~(interval(a,b) = {}) ==> (inv(&2) % (a + b)) IN interval(a,b)`,
  REWRITE_TAC[INTERVAL_NE_EMPTY; IN_INTERVAL] THEN
  SIMP_TAC[VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let OPEN_CLOSED_INTERVAL_CONVEX = prove
 (`!a b x y:real^N e.
        x IN interval(a,b) /\ y IN interval[a,b] /\ &0 < e /\ e <= &1
        ==> (e % x + (&1 - e) % y) IN interval(a,b)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(c /\ d ==> a /\ b ==> e) ==> a /\ b /\ c /\ d ==> e`) THEN
  STRIP_TAC THEN REWRITE_TAC[IN_INTERVAL; AND_FORALL_THM] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBST1_TAC(REAL_ARITH `(a:real^N)$i = e * a$i + (&1 - e) * a$i`) THEN
  SUBST1_TAC(REAL_ARITH `(b:real^N)$i = e * b$i + (&1 - e) * b$i`) THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LTE_ADD2 THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LE_LMUL; REAL_SUB_LE]);;

let CLOSURE_OPEN_INTERVAL = prove
 (`!a b:real^N.
     ~(interval(a,b) = {}) ==> closure(interval(a,b)) = interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN
    REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED; CLOSED_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; closure; IN_UNION] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~b ==> c) ==> b \/ c`) THEN DISCH_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; LIMPT_SEQUENTIAL] THEN
  ABBREV_TAC `(c:real^N) = inv(&2) % (a + b)` THEN
  EXISTS_TAC `\n. (x:real^N) + inv(&n + &1) % (c - x)` THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_DELETE] THEN
    REWRITE_TAC[VECTOR_ARITH `x + a = x <=> a = vec 0`] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0] THEN
    REWRITE_TAC[VECTOR_SUB_EQ; REAL_ARITH `~(&n + &1 = &0)`] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[OPEN_INTERVAL_MIDPOINT]] THEN
    REWRITE_TAC[VECTOR_ARITH `x + a % (y - x) = a % y + (&1 - a) % x`] THEN
    MATCH_MP_TAC OPEN_CLOSED_INTERVAL_CONVEX THEN
    CONJ_TAC THENL [ASM_MESON_TAC[OPEN_INTERVAL_MIDPOINT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [VECTOR_ARITH `x:real^N = x + &0 % (c - x)`] THEN
  MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST] THEN
  MATCH_MP_TAC LIM_VMUL THEN REWRITE_TAC[LIM_CONST] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY; o_THM; DIST_LIFT; REAL_SUB_RZERO] THEN
  X_GEN_TAC `e:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN UNDISCH_TAC `N:num <= n` THEN
  UNDISCH_TAC `~(N = 0)` THEN
  REWRITE_TAC[GSYM LT_NZ; GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_LT] THEN
  REAL_ARITH_TAC);;

let CLOSURE_INTERVAL = prove
 (`(!a b. closure(interval[a,b]) = interval[a,b]) /\
   (!a b. closure(interval(a,b)) =
          if interval(a,b) = {} then {} else interval[a,b])`,
  SIMP_TAC[CLOSURE_CLOSED; CLOSED_INTERVAL] THEN REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[CLOSURE_OPEN_INTERVAL; CLOSURE_EMPTY]);;

let BOUNDED_SUBSET_OPEN_INTERVAL_SYMMETRIC = prove
 (`!s:real^N->bool. bounded s ==> ?a. s SUBSET interval(--a,a)`,
  REWRITE_TAC[BOUNDED_POS; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `B:real`] THEN STRIP_TAC THEN
  EXISTS_TAC `(lambda i. B + &1):real^N` THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; REAL_BOUNDS_LT; VECTOR_NEG_COMPONENT] THEN
  ASM_MESON_TAC[COMPONENT_LE_NORM;
                REAL_ARITH `x <= y ==> a <= x ==> a < y + &1`]);;

let BOUNDED_SUBSET_OPEN_INTERVAL = prove
 (`!s:real^N->bool. bounded s ==> ?a b. s SUBSET interval(a,b)`,
  MESON_TAC[BOUNDED_SUBSET_OPEN_INTERVAL_SYMMETRIC]);;

let BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC = prove
 (`!s:real^N->bool. bounded s ==> ?a. s SUBSET interval[--a,a]`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUBSET_OPEN_INTERVAL_SYMMETRIC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  SIMP_TAC[IN_BALL; IN_INTERVAL; SUBSET; REAL_LT_IMP_LE]);;

let BOUNDED_SUBSET_CLOSED_INTERVAL = prove
 (`!s:real^N->bool. bounded s ==> ?a b. s SUBSET interval[a,b]`,
  MESON_TAC[BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC]);;

let FRONTIER_CLOSED_INTERVAL = prove
 (`!a b. frontier(interval[a,b]) = interval[a,b] DIFF interval(a,b)`,
  SIMP_TAC[frontier; INTERIOR_CLOSED_INTERVAL; CLOSURE_CLOSED;
           CLOSED_INTERVAL]);;

let FRONTIER_OPEN_INTERVAL = prove
 (`!a b. frontier(interval(a,b)) =
                if interval(a,b) = {} then {}
                else interval[a,b] DIFF interval(a,b)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[FRONTIER_EMPTY] THEN
  ASM_SIMP_TAC[frontier; CLOSURE_OPEN_INTERVAL; INTERIOR_OPEN;
               OPEN_INTERVAL]);;

let INTER_INTERVAL_MIXED_EQ_EMPTY = prove
 (`!a b c d:real^N.
        ~(interval(c,d) = {})
        ==> (interval(a,b) INTER interval[c,d] = {} <=>
             interval(a,b) INTER interval(c,d) = {})`,
  SIMP_TAC[GSYM CLOSURE_OPEN_INTERVAL; OPEN_INTER_CLOSURE_EQ_EMPTY;
           OPEN_INTERVAL]);;

let INTERVAL_TRANSLATION = prove
 (`(!c a b. interval[c + a,c + b] = IMAGE (\x. c + x) (interval[a,b])) /\
   (!c a b. interval(c + a,c + b) = IMAGE (\x. c + x) (interval(a,b)))`,
  REWRITE_TAC[interval] THEN CONJ_TAC THEN GEOM_TRANSLATE_TAC[] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; REAL_LT_LADD; REAL_LE_LADD]);;

add_translation_invariants
 [CONJUNCT1 INTERVAL_TRANSLATION; CONJUNCT2 INTERVAL_TRANSLATION];;

let EMPTY_AS_INTERVAL = prove
 (`{} = interval[vec 1,vec 0]`,
  SIMP_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTERVAL; VEC_COMPONENT] THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
  REWRITE_TAC[LE_REFL; DIMINDEX_GE_1] THEN REAL_ARITH_TAC);;

let UNIT_INTERVAL_NONEMPTY = prove
 (`~(interval[vec 0:real^N,vec 1] = {}) /\
   ~(interval(vec 0:real^N,vec 1) = {})`,
  SIMP_TAC[INTERVAL_NE_EMPTY; VEC_COMPONENT; REAL_LT_01; REAL_POS]);;

let IMAGE_STRETCH_INTERVAL = prove
 (`!a b:real^N m.
    IMAGE (\x. lambda k. m(k) * x$k) (interval[a,b]) =
        if interval[a,b] = {} then {}
        else interval[(lambda k. min (m(k) * a$k) (m(k) * b$k)):real^N,
                      (lambda k. max (m(k) * a$k) (m(k) * b$k))]`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[IMAGE_CLAUSES] THEN
  ASM_SIMP_TAC[EXTENSION; IN_IMAGE; CART_EQ; IN_INTERVAL; AND_FORALL_THM;
               TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`;
                LAMBDA_BETA; GSYM LAMBDA_SKOLEM] THEN
  X_GEN_TAC `x:real^N` THEN MATCH_MP_TAC(MESON[]
   `(!x. p x ==> (q x <=> r x))
    ==> ((!x. p x ==> q x) <=> (!x. p x ==> r x))`) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INTERVAL_NE_EMPTY]) THEN
  MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `k:num` THEN ASM_CASES_TAC `1 <= k /\ k <= dimindex(:N)` THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `(m:num->real) k = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MAX_ACI; REAL_MIN_ACI] THEN
    ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(m = &0) ==> (x = m * y <=> y = x / m)`] THEN
  REWRITE_TAC[UNWIND_THM2] THEN FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP
   (REAL_ARITH `~(z = &0) ==> &0 < z \/ &0 < --z`))
  THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM REAL_LE_NEG2] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_ARITH `--(max a b) = min (--a) (--b)`;
                REAL_ARITH `--(min a b) = max (--a) (--b)`; real_div;
                GSYM REAL_MUL_RNEG; GSYM REAL_INV_NEG] THEN
    REWRITE_TAC[GSYM real_div]] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
  ASM_SIMP_TAC[real_min; real_max; REAL_LE_LMUL_EQ; REAL_LE_RMUL_EQ] THEN
  REAL_ARITH_TAC);;

let INTERVAL_IMAGE_STRETCH_INTERVAL = prove
 (`!a b:real^N m. ?u v:real^N.
     IMAGE (\x. lambda k. m k * x$k) (interval[a,b]) = interval[u,v]`,
  REWRITE_TAC[IMAGE_STRETCH_INTERVAL] THEN MESON_TAC[EMPTY_AS_INTERVAL]);;

let CLOSED_INTERVAL_IMAGE_UNIT_INTERVAL = prove
 (`!a b:real^N.
        ~(interval[a,b] = {})
        ==> interval[a,b] = IMAGE (\x:real^N. a + x)
                                  (IMAGE (\x. (lambda i. (b$i - a$i) * x$i))
                                         (interval[vec 0:real^N,vec 1]))`,
  REWRITE_TAC[INTERVAL_NE_EMPTY] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[IMAGE_STRETCH_INTERVAL; UNIT_INTERVAL_NONEMPTY] THEN
  REWRITE_TAC[GSYM INTERVAL_TRANSLATION] THEN
  REWRITE_TAC[EXTENSION; IN_INTERVAL] THEN
  SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VEC_COMPONENT] THEN
  GEN_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID] THEN
  MATCH_MP_TAC(MESON[] `(!x. P x <=> Q x) ==> ((!x. P x) <=> (!x. Q x))`) THEN
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `1 <= i /\ i <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let SUMS_INTERVALS = prove
 (`(!a b c d:real^N.
        ~(interval[a,b] = {}) /\ ~(interval[c,d] = {})
        ==> {x + y | x IN interval[a,b] /\ y IN interval[c,d]} =
            interval[a+c,b+d]) /\
   (!a b c d:real^N.
        ~(interval(a,b) = {}) /\ ~(interval(c,d) = {})
        ==> {x + y | x IN interval(a,b) /\ y IN interval(c,d)} =
            interval(a+c,b+d))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[INTERVAL_NE_EMPTY] THEN
  STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_INTERVAL; IN_ELIM_THM] THEN
  REWRITE_TAC[TAUT `(a /\ b) /\ c <=> c /\ a /\ b`] THEN
  REWRITE_TAC[VECTOR_ARITH `x:real^N = y + z <=> z = x - y`] THEN
  REWRITE_TAC[UNWIND_THM2; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT] THEN
  (X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC);
    DISCH_TAC THEN
    REWRITE_TAC[AND_FORALL_THM; GSYM LAMBDA_SKOLEM;
                TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
    REWRITE_TAC[REAL_ARITH
     `((a <= y /\ y <= b) /\ c <= x - y /\ x - y <= d <=>
       max a (x - d) <= y /\ y <= min b (x - c)) /\
      ((a < y /\ y < b) /\ c < x - y /\ x - y < d <=>
       max a (x - d) < y /\ y < min b (x - c))`] THEN
    REWRITE_TAC[GSYM REAL_LE_BETWEEN; GSYM REAL_LT_BETWEEN]] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC));;

let PCROSS_INTERVAL = prove
 (`!a b:real^M c d:real^N.
        interval[a,b] PCROSS interval[c,d] =
        interval[pastecart a c,pastecart b d]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PCROSS] THEN
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_PASTECART_THM] THEN
  SIMP_TAC[IN_INTERVAL; pastecart; LAMBDA_BETA; DIMINDEX_FINITE_SUM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^N`] THEN EQ_TAC THEN STRIP_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    CONJ_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `i + dimindex(:M)`) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_SUB] THENL
       [ASM_ARITH_TAC;
        DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]]]);;

let OPEN_CONTAINS_INTERVAL,OPEN_CONTAINS_OPEN_INTERVAL = (CONJ_PAIR o prove)
 (`(!s:real^N->bool.
        open s <=>
        !x. x IN s ==> ?a b. x IN interval(a,b) /\ interval[a,b] SUBSET s) /\
   (!s:real^N->bool.
        open s <=>
        !x. x IN s ==> ?a b. x IN interval(a,b) /\ interval(a,b) SUBSET s)`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC(TAUT
   `(q ==> r) /\ (r ==> p) /\ (p ==> q) ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[SUBSET_TRANS; INTERVAL_OPEN_SUBSET_CLOSED];
    DISCH_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `interval(a:real^N,b)` OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[OPEN_INTERVAL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET_TRANS; INTERVAL_OPEN_SUBSET_CLOSED];
    DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o
      GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x - e / &(dimindex(:N)) % vec 1:real^N` THEN
    EXISTS_TAC `x + e / &(dimindex(:N)) % vec 1:real^N` THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `b SUBSET s ==> x IN i /\ j SUBSET b ==> x IN i /\ j SUBSET s`)) THEN
    SIMP_TAC[IN_INTERVAL; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; IN_CBALL;
             VEC_COMPONENT; VECTOR_ADD_COMPONENT; SUBSET; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH `x - e < x /\ x < x + e <=> &0 < e`;
                REAL_ARITH `x - e <= y /\ y <= x + e <=> abs(x - y) <= e`] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1] THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
    DISCH_TAC THEN REWRITE_TAC[dist] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. abs((x - y:real^N)$i))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_BOUND_GEN THEN
    ASM_SIMP_TAC[CARD_NUMSEG_1; IN_NUMSEG; FINITE_NUMSEG] THEN
    REWRITE_TAC[NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1]]);;

let DIAMETER_INTERVAL = prove
 (`(!a b:real^N.
        diameter(interval[a,b]) =
        if interval[a,b] = {} then &0 else norm(b - a)) /\
   (!a b:real^N.
        diameter(interval(a,b)) =
        if interval(a,b) = {} then &0 else norm(b - a))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
   [ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET_EMPTY; DIAMETER_EMPTY];
    ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    ASM_SIMP_TAC[DIAMETER_BOUNDED_BOUND;
                 ENDS_IN_INTERVAL; BOUNDED_INTERVAL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `diameter(cball(inv(&2) % (a + b):real^N,norm(b - a) / &2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIAMETER_SUBSET THEN REWRITE_TAC[BOUNDED_CBALL] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL; IN_CBALL] THEN
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[dist] THEN
      REWRITE_TAC[GSYM NORM_MUL; REAL_ARITH `x / &2 = abs(inv(&2)) * x`] THEN
      MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
      ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
                      VECTOR_MUL_COMPONENT] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[DIAMETER_CBALL] THEN NORM_ARITH_TAC];
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[DIAMETER_EMPTY] THEN
    SUBGOAL_THEN `interval[a:real^N,b] = closure(interval(a,b))`
    SUBST_ALL_TAC THEN ASM_REWRITE_TAC[CLOSURE_INTERVAL] THEN
    ASM_MESON_TAC[DIAMETER_CLOSURE; BOUNDED_INTERVAL]]);;

let IMAGE_TWIZZLE_INTERVAL = prove
 (`!p a b. dimindex(:M) = dimindex(:N) /\ p permutes 1..dimindex(:N)
           ==> IMAGE ((\x. lambda i. x$(p i)):real^M->real^N) (interval[a,b]) =
               interval[(lambda i. a$(p i)),(lambda i. b$(p i))]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  SIMP_TAC[IN_INTERVAL; CART_EQ; LAMBDA_BETA] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `(lambda i. (y:real^N)$(inverse p i)):real^M` THEN
    IMP_REWRITE_TAC[LAMBDA_BETA] THEN
    ASM_REWRITE_TAC[GSYM IN_NUMSEG] THEN
    ASM_MESON_TAC[PERMUTES_INVERSE_EQ; PERMUTES_IN_IMAGE];
    REWRITE_TAC[GSYM IN_NUMSEG] THEN
    ASM_MESON_TAC[PERMUTES_INVERSES; PERMUTES_IN_IMAGE]]);;

(* ------------------------------------------------------------------------- *)
(* Some special cases for intervals in R^1.                                  *)
(* ------------------------------------------------------------------------- *)

let INTERVAL_CASES_1 = prove
 (`!x:real^1. x IN interval[a,b] ==> x IN interval(a,b) \/ (x = a) \/ (x = b)`,
  REWRITE_TAC[CART_EQ; IN_INTERVAL; FORALL_DIMINDEX_1] THEN REAL_ARITH_TAC);;

let IN_INTERVAL_1 = prove
 (`!a b x:real^1.
        (x IN interval[a,b] <=> drop a <= drop x /\ drop x <= drop b) /\
        (x IN interval(a,b) <=> drop a < drop x /\ drop x < drop b)`,
  REWRITE_TAC[IN_INTERVAL; drop; CONJ_ASSOC; DIMINDEX_1; LE_ANTISYM] THEN
  MESON_TAC[]);;

let INTERVAL_EQ_EMPTY_1 = prove
 (`!a b:real^1.
        (interval[a,b] = {} <=> drop b < drop a) /\
        (interval(a,b) = {} <=> drop b <= drop a)`,
  REWRITE_TAC[INTERVAL_EQ_EMPTY; drop; CONJ_ASSOC; DIMINDEX_1; LE_ANTISYM] THEN
  MESON_TAC[]);;

let INTERVAL_NE_EMPTY_1 = prove
 (`(!a b:real^1. ~(interval[a,b] = {}) <=> drop a <= drop b) /\
   (!a b:real^1. ~(interval(a,b) = {}) <=> drop a < drop b)`,
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1] THEN REAL_ARITH_TAC);;

let SUBSET_INTERVAL_1 = prove
 (`!a b c d.
        (interval[a,b] SUBSET interval[c,d] <=>
                drop b < drop a \/
                drop c <= drop a /\ drop a <= drop b /\ drop b <= drop d) /\
        (interval[a,b] SUBSET interval(c,d) <=>
                drop b < drop a \/
                drop c < drop a /\ drop a <= drop b /\ drop b < drop d) /\
        (interval(a,b) SUBSET interval[c,d] <=>
                drop b <= drop a \/
                drop c <= drop a /\ drop a < drop b /\ drop b <= drop d) /\
        (interval(a,b) SUBSET interval(c,d) <=>
                drop b <= drop a \/
                drop c <= drop a /\ drop a < drop b /\ drop b <= drop d)`,
  REWRITE_TAC[SUBSET_INTERVAL; FORALL_1; DIMINDEX_1; drop] THEN
  REAL_ARITH_TAC);;

let EQ_INTERVAL_1 = prove
 (`!a b c d:real^1.
       (interval[a,b] = interval[c,d] <=>
          drop b < drop a /\ drop d < drop c \/
          drop a = drop c /\ drop b = drop d)`,
  REWRITE_TAC[SET_RULE `s = t <=> s SUBSET t /\ t SUBSET s`] THEN
  REWRITE_TAC[SUBSET_INTERVAL_1] THEN REAL_ARITH_TAC);;

let DISJOINT_INTERVAL_1 = prove
 (`!a b c d:real^1.
        (interval[a,b] INTER interval[c,d] = {} <=>
          drop b < drop a \/ drop d < drop c \/
          drop b < drop c \/ drop d < drop a) /\
        (interval[a,b] INTER interval(c,d) = {} <=>
          drop b < drop a \/ drop d <= drop c \/
          drop b <= drop c \/ drop d <= drop a) /\
        (interval(a,b) INTER interval[c,d] = {} <=>
          drop b <= drop a \/ drop d < drop c \/
          drop b <= drop c \/ drop d <= drop a) /\
        (interval(a,b) INTER interval(c,d) = {} <=>
          drop b <= drop a \/ drop d <= drop c \/
          drop b <= drop c \/ drop d <= drop a)`,
  REWRITE_TAC[DISJOINT_INTERVAL; CONJ_ASSOC; DIMINDEX_1; LE_ANTISYM;
              UNWIND_THM1; drop]);;

let OPEN_CLOSED_INTERVAL_1 = prove
 (`!a b:real^1. interval(a,b) = interval[a,b] DIFF {a,b}`,
  REWRITE_TAC[EXTENSION; IN_INTERVAL_1; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[GSYM DROP_EQ] THEN REAL_ARITH_TAC);;

let CLOSED_OPEN_INTERVAL_1 = prove
 (`!a b:real^1. drop a <= drop b ==> interval[a,b] = interval(a,b) UNION {a,b}`,
  REWRITE_TAC[EXTENSION; IN_INTERVAL_1; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[GSYM DROP_EQ] THEN REAL_ARITH_TAC);;

let BALL_1 = prove
 (`!x:real^1 r. cball(x,r) = interval[x - lift r,x + lift r] /\
                ball(x,r) = interval(x - lift r,x + lift r)`,
  REWRITE_TAC[EXTENSION; IN_BALL; IN_CBALL; IN_INTERVAL_1] THEN
  REWRITE_TAC[dist; NORM_REAL; GSYM drop; DROP_SUB; LIFT_DROP; DROP_ADD] THEN
  REAL_ARITH_TAC);;

let SPHERE_1 = prove
 (`!a:real^1 r. sphere(a,r) = if r < &0 then {} else {a - lift r,a + lift r}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sphere] THEN COND_CASES_TAC THEN
  REWRITE_TAC[DIST_REAL; GSYM drop; FORALL_DROP] THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_SUB; LIFT_DROP] THEN
  ASM_REAL_ARITH_TAC);;

let FINITE_SPHERE_1 = prove
 (`!a:real^1 r. FINITE(sphere(a,r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SPHERE_1] THEN
  MESON_TAC[FINITE_INSERT; FINITE_EMPTY]);;

let FINITE_INTERVAL_1 = prove
 (`(!a b. FINITE(interval[a,b]) <=> drop b <= drop a) /\
   (!a b. FINITE(interval(a,b)) <=> drop b <= drop a)`,
  REWRITE_TAC[OPEN_CLOSED_INTERVAL_1] THEN
  REWRITE_TAC[SET_RULE `s DIFF {a,b} = s DELETE a DELETE b`] THEN
  REWRITE_TAC[FINITE_DELETE] THEN REPEAT GEN_TAC THEN
  SUBGOAL_THEN `interval[a,b] = IMAGE lift {x | drop a <= x /\ x <= drop b}`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    CONJ_TAC THENL [MESON_TAC[LIFT_DROP]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_ELIM_THM; LIFT_DROP];
    SIMP_TAC[FINITE_IMAGE_INJ_EQ; LIFT_EQ; FINITE_REAL_INTERVAL]]);;

let BALL_INTERVAL = prove
 (`!x:real^1 e. ball(x,e) = interval(x - lift e,x + lift e)`,
  REWRITE_TAC[EXTENSION; IN_BALL; IN_INTERVAL_1; DIST_REAL] THEN
  REWRITE_TAC[GSYM drop; DROP_SUB; DROP_ADD; LIFT_DROP] THEN REAL_ARITH_TAC);;

let CBALL_INTERVAL = prove
 (`!x:real^1 e. cball(x,e) = interval[x - lift e,x + lift e]`,
  REWRITE_TAC[EXTENSION; IN_CBALL; IN_INTERVAL_1; DIST_REAL] THEN
  REWRITE_TAC[GSYM drop; DROP_SUB; DROP_ADD; LIFT_DROP] THEN REAL_ARITH_TAC);;

let BALL_INTERVAL_0 = prove
 (`!e. ball(vec 0:real^1,e) = interval(--lift e,lift e)`,
  GEN_TAC THEN REWRITE_TAC[BALL_INTERVAL] THEN AP_TERM_TAC THEN
  BINOP_TAC THEN VECTOR_ARITH_TAC);;

let CBALL_INTERVAL_0 = prove
 (`!e. cball(vec 0:real^1,e) = interval[--lift e,lift e]`,
  GEN_TAC THEN REWRITE_TAC[CBALL_INTERVAL] THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN BINOP_TAC THEN VECTOR_ARITH_TAC);;

let INTER_INTERVAL_1 = prove
 (`!a b c d:real^1.
        interval[a,b] INTER interval[c,d] =
        interval[lift(max (drop a) (drop c)),lift(min (drop b) (drop d))]`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_INTERVAL_1; real_max; real_min] THEN
  REPEAT GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[LIFT_DROP]) THEN
  ASM_REAL_ARITH_TAC);;

let CLOSED_DIFF_OPEN_INTERVAL_1 = prove
 (`!a b:real^1.
        interval[a,b] DIFF interval(a,b) =
        if interval[a,b] = {} then {} else {a,b}`,
  REWRITE_TAC[EXTENSION; IN_DIFF; INTERVAL_EQ_EMPTY_1; IN_INTERVAL_1] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Intervals in general, including infinite and mixtures of open and closed. *)
(* ------------------------------------------------------------------------- *)

let is_interval = new_definition
  `is_interval(s:real^N->bool) <=>
        !a b x. a IN s /\ b IN s /\
                (!i. 1 <= i /\ i <= dimindex(:N)
                     ==> (a$i <= x$i /\ x$i <= b$i) \/
                         (b$i <= x$i /\ x$i <= a$i))
                ==> x IN s`;;

let IS_INTERVAL_INTERVAL = prove
 (`!a:real^N b. is_interval(interval (a,b)) /\ is_interval(interval [a,b])`,
  REWRITE_TAC[is_interval; IN_INTERVAL] THEN
  MESON_TAC[REAL_LT_TRANS; REAL_LE_TRANS; REAL_LET_TRANS; REAL_LTE_TRANS]);;

let IS_INTERVAL_EMPTY = prove
 (`is_interval {}`,
  REWRITE_TAC[is_interval; NOT_IN_EMPTY]);;

let IS_INTERVAL_UNIV = prove
 (`is_interval(UNIV:real^N->bool)`,
  REWRITE_TAC[is_interval; IN_UNIV]);;

let IS_INTERVAL_TRANSLATION_EQ = prove
 (`!a:real^N s. is_interval(IMAGE (\x. a + x) s) <=> is_interval s`,
  REWRITE_TAC[is_interval] THEN GEOM_TRANSLATE_TAC[] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; REAL_LT_LADD; REAL_LE_LADD]);;

add_translation_invariants [IS_INTERVAL_TRANSLATION_EQ];;

let IS_INTERVAL_TRANSLATION = prove
 (`!s a:real^N. is_interval s ==> is_interval(IMAGE (\x. a + x) s)`,
  REWRITE_TAC[IS_INTERVAL_TRANSLATION_EQ]);;

let IS_INTERVAL_POINTWISE = prove
 (`!s:real^N->bool x.
        is_interval s /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> ?a. a IN s /\ a$i = x$i)
        ==> x IN s`,
  REWRITE_TAC[is_interval] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `!n. ?y:real^N. (!i. 1 <= i /\ i <= n ==> y$i = (x:real^N)$i) /\ y IN s`
  MP_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[ARITH_RULE `~(1 <= i /\ i <= 0)`] THENL
     [ASM_MESON_TAC[DIMINDEX_GE_1; LE_REFL]; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `y:real^N`) THEN
    ASM_CASES_TAC `SUC n <= dimindex(:N)` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC
       `(lambda i. if i <= n then (y:real^N)$i else (z:real^N)$i):real^N` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        SUBGOAL_THEN `i <= dimindex(:N)` ASSUME_TAC THENL
         [ASM_ARITH_TAC; ASM_SIMP_TAC[LAMBDA_BETA]] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `i = SUC n` (fun th -> ASM_REWRITE_TAC[th]) THEN
        ASM_ARITH_TAC;
        FIRST_X_ASSUM(ASSUME_TAC o CONJUNCT2) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`y:real^N`; `z:real^N`] THEN
        ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC];
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `y:real^N = x` (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[CART_EQ] THEN
      ASM_MESON_TAC[ARITH_RULE `i <= N /\ ~(SUC n <= N) ==> i <= n`]];
    DISCH_THEN(MP_TAC o SPEC `dimindex(:N)`) THEN
    REWRITE_TAC[GSYM CART_EQ] THEN MESON_TAC[]]);;

let IS_INTERVAL_COMPACT = prove
 (`!s:real^N->bool. is_interval s /\ compact s <=> ?a b. s = interval[a,b]`,
  GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[IS_INTERVAL_INTERVAL; COMPACT_INTERVAL] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_MESON_TAC[EMPTY_AS_INTERVAL]; ALL_TAC] THEN
  EXISTS_TAC `(lambda i. inf { (x:real^N)$i | x IN s}):real^N` THEN
  EXISTS_TAC `(lambda i. sup { (x:real^N)$i | x IN s}):real^N` THEN
  SIMP_TAC[EXTENSION; IN_INTERVAL; LAMBDA_BETA] THEN X_GEN_TAC `x:real^N` THEN
  EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPEC `{ (x:real^N)$i | x IN s}` INF) THEN
    MP_TAC(ISPEC `{ (x:real^N)$i | x IN s}` SUP) THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
    REWRITE_TAC[bounded] THEN
    ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS; MEMBER_NOT_EMPTY;
                  REAL_ARITH `abs(x) <= B ==> --B <= x /\ x <= B`];
    DISCH_TAC THEN MATCH_MP_TAC IS_INTERVAL_POINTWISE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?a b:real^N. a IN s /\ b IN s /\ a$i <= (x:real^N)$i /\ x$i <= b$i`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`\x:real^N. x$i`; `s:real^N->bool`]
        CONTINUOUS_ATTAINS_INF) THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; o_DEF] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`\x:real^N. x$i`; `s:real^N->bool`]
        CONTINUOUS_ATTAINS_SUP) THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; o_DEF] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
       [EXISTS_TAC `inf {(x:real^N)$i | x IN s}` THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC REAL_LE_INF THEN ASM SET_TAC[];
        EXISTS_TAC `sup {(x:real^N)$i | x IN s}` THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC REAL_SUP_LE THEN ASM SET_TAC[]];
      EXISTS_TAC
       `(lambda j. if j = i then (x:real^N)$i else (a:real^N)$j):real^N` THEN
      ASM_SIMP_TAC[LAMBDA_BETA] THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[is_interval]) THEN
      MAP_EVERY EXISTS_TAC
       [`a:real^N`;
        `(lambda j. if j = i then (b:real^N)$i else (a:real^N)$j):real^N`] THEN
      ASM_SIMP_TAC[LAMBDA_BETA] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[is_interval]) THEN
        MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
        ASM_SIMP_TAC[LAMBDA_BETA];
        ALL_TAC] THEN
      GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC]]);;

let IS_INTERVAL_1 = prove
 (`!s:real^1->bool.
        is_interval s <=>
          !a b x. a IN s /\ b IN s /\ drop a <= drop x /\ drop x <= drop b
                  ==> x IN s`,
  REWRITE_TAC[is_interval; DIMINDEX_1; FORALL_1; GSYM drop] THEN
  REWRITE_TAC[FORALL_LIFT; LIFT_DROP] THEN MESON_TAC[]);;

let IS_INTERVAL_1_CASES = prove
 (`!s:real^1->bool.
        is_interval s <=>
        s = {} \/
        s = (:real^1) \/
        (?a. s = {x | a < drop x}) \/
        (?a. s = {x | a <= drop x}) \/
        (?b. s = {x | drop x <= b}) \/
        (?b. s = {x | drop x < b}) \/
        (?a b. s = {x | a < drop x /\ drop x < b}) \/
        (?a b. s = {x | a < drop x /\ drop x <= b}) \/
        (?a b. s = {x | a <= drop x /\ drop x < b}) \/
        (?a b. s = {x | a <= drop x /\ drop x <= b})`,
  GEN_TAC THEN REWRITE_TAC[IS_INTERVAL_1] THEN EQ_TAC THENL
   [DISCH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV; NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC] THEN
  ASM_CASES_TAC `s:real^1->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `IMAGE drop s` SUP) THEN
  MP_TAC(ISPEC `IMAGE drop s` INF) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  ASM_CASES_TAC `?a. !x. x IN s ==> a <= drop x` THEN
  ASM_CASES_TAC `?b. !x. x IN s ==> drop x <= b` THEN
  ASM_REWRITE_TAC[] THENL
   [STRIP_TAC THEN STRIP_TAC THEN
    MAP_EVERY ASM_CASES_TAC
     [`inf(IMAGE drop s) IN IMAGE drop s`; `sup(IMAGE drop s) IN IMAGE drop s`]
    THENL
     [REPLICATE_TAC 8 DISJ2_TAC;
      REPLICATE_TAC 7 DISJ2_TAC THEN DISJ1_TAC;
      REPLICATE_TAC 6 DISJ2_TAC THEN DISJ1_TAC;
      REPLICATE_TAC 5 DISJ2_TAC THEN DISJ1_TAC] THEN
    MAP_EVERY EXISTS_TAC [`inf(IMAGE drop s)`; `sup(IMAGE drop s)`];
    STRIP_TAC THEN ASM_CASES_TAC `inf(IMAGE drop s) IN IMAGE drop s` THENL
     [REPLICATE_TAC 2 DISJ2_TAC THEN DISJ1_TAC;
      DISJ2_TAC THEN DISJ1_TAC] THEN
    EXISTS_TAC `inf(IMAGE drop s)`;
    STRIP_TAC THEN ASM_CASES_TAC `sup(IMAGE drop s) IN IMAGE drop s` THENL
     [REPLICATE_TAC 3 DISJ2_TAC THEN DISJ1_TAC;
      REPLICATE_TAC 4 DISJ2_TAC THEN DISJ1_TAC] THEN
    EXISTS_TAC `sup(IMAGE drop s)`;
    DISJ1_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_IMAGE]) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_TOTAL; REAL_LE_ANTISYM]);;

let IS_INTERVAL_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        is_interval s /\ is_interval t ==> is_interval(s PCROSS t)`,
  REWRITE_TAC[is_interval; DIMINDEX_FINITE_SUM] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(MESON[]
   `(!a b a' b' x x'. P a b x /\ Q a' b' x' ==> R a b x a' b' x')
    ==> (!a b x. P a b x) /\ (!a' b' x'. Q a' b' x')
        ==> (!a a' b b' x x'. R a b x a' b' x')`) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_SIMP_TAC[pastecart; LAMBDA_BETA; DIMINDEX_FINITE_SUM;
                 ARITH_RULE `x:num <= m ==> x <= m + n`];
    FIRST_X_ASSUM(MP_TAC o SPEC `dimindex(:M) + i`) THEN
    ASM_SIMP_TAC[pastecart; LAMBDA_BETA; DIMINDEX_FINITE_SUM;
                 ARITH_RULE `x:num <= n ==> m + x <= m + n`;
                 ARITH_RULE `1 <= x ==> 1 <= m + x`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_SUB2] THEN ASM_ARITH_TAC]);;

let IS_INTERVAL_PCROSS_EQ = prove
 (`!s:real^M->bool t:real^N->bool.
        is_interval(s PCROSS t) <=>
        s = {} \/ t = {} \/ is_interval s /\ is_interval t`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; IS_INTERVAL_EMPTY] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; IS_INTERVAL_EMPTY] THEN
  EQ_TAC THEN REWRITE_TAC[IS_INTERVAL_PCROSS] THEN
  REWRITE_TAC[is_interval] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `x:real^M`] THEN
    STRIP_TAC THEN UNDISCH_TAC `~(t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`a:real^M`; `y:real^N`; `b:real^M`;
      `y:real^N`; `x:real^M`; `y:real^N`]);
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `x:real^N`] THEN
    STRIP_TAC THEN UNDISCH_TAC `~(s:real^M->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `w:real^M`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`w:real^M`; `a:real^N`; `w:real^M`;
      `b:real^N`; `w:real^M`; `x:real^N`])] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  SIMP_TAC[pastecart; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_MESON_TAC[DIMINDEX_FINITE_SUM; ARITH_RULE
      `1 <= i /\ i <= m + n /\ ~(i <= m) ==> 1 <= i - m /\ i - m <= n`]);;

let IS_INTERVAL_INTER = prove
 (`!s t:real^N->bool.
        is_interval s /\ is_interval t ==> is_interval(s INTER t)`,
  REWRITE_TAC[is_interval; IN_INTER] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `x:real^N`] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[]);;

let INTERVAL_SUBSET_IS_INTERVAL = prove
 (`!s a b:real^N.
     is_interval s
     ==> (interval[a,b] SUBSET s <=> interval[a,b] = {} \/ a IN s /\ b IN s)`,
  REWRITE_TAC[is_interval] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interval[a:real^N,b] = {}` THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
  EQ_TAC THENL [ASM_MESON_TAC[ENDS_IN_INTERVAL; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTERVAL] THEN ASM_MESON_TAC[]);;

let INTERVAL_CONTAINS_COMPACT_NEIGHBOURHOOD = prove
 (`!s x:real^N.
        is_interval s /\ x IN s
        ==> ?a b d. &0 < d /\ x IN interval[a,b] /\
                    interval[a,b] SUBSET s /\
                    ball(x,d) INTER s SUBSET interval[a,b]`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INTERVAL_SUBSET_IS_INTERVAL] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> ?a. (?y. y IN s /\ y$i = a) /\
                (a < x$i \/ a = (x:real^N)$i /\
                            !y:real^N. y IN s ==> a <= y$i)`
  MP_TAC THENL [ASM_MESON_TAC[REAL_NOT_LT]; REWRITE_TAC[LAMBDA_SKOLEM]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> ?b. (?y. y IN s /\ y$i = b) /\
                (x$i < b \/ b = (x:real^N)$i /\
                            !y:real^N. y IN s ==> y$i <= b)`
  MP_TAC THENL [ASM_MESON_TAC[REAL_NOT_LT]; REWRITE_TAC[LAMBDA_SKOLEM]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N` THEN STRIP_TAC THEN
  EXISTS_TAC `min (inf (IMAGE (\i. if a$i < x$i
                                   then (x:real^N)$i - (a:real^N)$i else &1)
                              (1..dimindex(:N))))
                  (inf (IMAGE (\i. if x$i < b$i
                                   then (b:real^N)$i - x$i else &1)
                              (1..dimindex(:N))))` THEN
  REWRITE_TAC[REAL_LT_MIN; SUBSET; IN_BALL; IN_INTER] THEN
  SIMP_TAC[REAL_LT_INF_FINITE; IMAGE_EQ_EMPTY; FINITE_IMAGE;
           FINITE_NUMSEG; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_INTERVAL] THEN REPEAT CONJ_TAC THENL
   [MESON_TAC[REAL_SUB_LT; REAL_LT_01];
    MESON_TAC[REAL_SUB_LT; REAL_LT_01];
    ASM_MESON_TAC[REAL_LE_LT];
    DISJ2_TAC THEN CONJ_TAC THEN MATCH_MP_TAC IS_INTERVAL_POINTWISE THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC `i:num` THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
    (COND_CASES_TAC THENL [REWRITE_TAC[dist]; ASM_MESON_TAC[]]) THEN
    DISCH_TAC THEN MP_TAC(ISPECL [`x - y:real^N`; `i:num`]
      COMPONENT_LE_NORM) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC]);;

let IS_INTERVAL_SUMS = prove
 (`!s t:real^N->bool.
        is_interval s /\ is_interval t
        ==> is_interval {x + y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[is_interval] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  MAP_EVERY X_GEN_TAC
   [`a:real^N`; `a':real^N`; `b:real^N`; `b':real^N`; `y:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o SPECL [`a:real^N`; `b:real^N`]) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o SPECL [`a':real^N`; `b':real^N`]) STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[IMP_IMP; IN_ELIM_THM] THEN  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `z:real^N = x + y <=> y = z - x`] THEN
  REWRITE_TAC[UNWIND_THM2] THEN MATCH_MP_TAC(MESON[]
   `(?x. P x /\ Q(f x))
    ==> (!x. P x ==> x IN s) /\ (!x. Q x ==> x IN t)
        ==> ?x. x IN s /\ f x IN t`) THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT; AND_FORALL_THM;
              TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REWRITE_TAC[GSYM LAMBDA_SKOLEM] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH
   `c <= y - x /\ y - x <= d <=> y - d <= x /\ x <= y - c`] THEN
  REWRITE_TAC[REAL_ARITH
  `a <= x /\ x <= b \/ b <= x /\ x <= a <=> min a b <= x /\ x <= max a b`] THEN
  ONCE_REWRITE_TAC[TAUT `(p /\ q) /\ (r /\ s) <=> (p /\ r) /\ (q /\ s)`] THEN
  REWRITE_TAC[GSYM REAL_LE_MIN; GSYM REAL_MAX_LE] THEN
  REWRITE_TAC[GSYM REAL_LE_BETWEEN] THEN REAL_ARITH_TAC);;

let IS_INTERVAL_SING = prove
 (`!a:real^N. is_interval {a}`,
  SIMP_TAC[is_interval; IN_SING; IMP_CONJ; CART_EQ; REAL_LE_ANTISYM]);;

let IS_INTERVAL_SCALING = prove
 (`!s:real^N->bool c. is_interval s ==> is_interval(IMAGE (\x. c % x) s)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    SUBGOAL_THEN `IMAGE ((\x. vec 0):real^N->real^N) s = {} \/
                  IMAGE ((\x. vec 0):real^N->real^N) s = {vec 0}`
    STRIP_ASSUME_TAC THENL
     [SET_TAC[];
      ASM_REWRITE_TAC[IS_INTERVAL_EMPTY];
      ASM_REWRITE_TAC[IS_INTERVAL_SING]];
    REWRITE_TAC[is_interval; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    GEN_REWRITE_TAC (BINOP_CONV o REDEPTH_CONV) [RIGHT_IMP_FORALL_THM] THEN
    REWRITE_TAC[IMP_IMP; VECTOR_MUL_COMPONENT] THEN
    MAP_EVERY (fun t -> MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC t)
     [`a:real^N`; `b:real^N`] THEN
    DISCH_THEN(fun th -> X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
                         MP_TAC(SPEC `inv(c) % x:real^N` th)) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; IN_IMAGE] THEN ANTS_TAC THENL
     [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
       `~(c = &0) ==> &0 < c \/ &0 < --c`)) THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_LE_NEG2] THEN
      ASM_SIMP_TAC[GSYM REAL_MUL_RNEG; GSYM REAL_LE_RDIV_EQ; GSYM
                   REAL_LE_LDIV_EQ] THEN
      REWRITE_TAC[real_div; REAL_INV_NEG] THEN REAL_ARITH_TAC;
      DISCH_TAC THEN EXISTS_TAC `inv c % x:real^N` THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID]]]);;

let IS_INTERVAL_SCALING_EQ = prove
 (`!s:real^N->bool c.
        is_interval(IMAGE (\x. c % x) s) <=> c = &0 \/ is_interval s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    SUBGOAL_THEN `IMAGE ((\x. vec 0):real^N->real^N) s = {} \/
                  IMAGE ((\x. vec 0):real^N->real^N) s = {vec 0}`
    STRIP_ASSUME_TAC THENL
     [SET_TAC[];
      ASM_REWRITE_TAC[IS_INTERVAL_EMPTY];
      ASM_REWRITE_TAC[IS_INTERVAL_SING]];
    ASM_REWRITE_TAC[] THEN EQ_TAC THEN REWRITE_TAC[IS_INTERVAL_SCALING] THEN
    DISCH_THEN(MP_TAC o SPEC `inv c:real` o MATCH_MP IS_INTERVAL_SCALING) THEN
    ASM_SIMP_TAC[GSYM IMAGE_o; VECTOR_MUL_ASSOC; o_DEF; REAL_MUL_LINV;
                 VECTOR_MUL_LID; IMAGE_ID]]);;

let lemma = prove
 (`!c. &0 < c
       ==> !s:real^N->bool. is_interval(IMAGE (\x. c % x) s) <=>
                            is_interval s`,
  SIMP_TAC[IS_INTERVAL_SCALING_EQ; REAL_LT_IMP_NZ]) in
add_scaling_theorems [lemma];;

(* ------------------------------------------------------------------------- *)
(* Line segments, with same open/closed overloading as for intervals.        *)
(* ------------------------------------------------------------------------- *)

let closed_segment = define
 `closed_segment[a,b] = {(&1 - u) % a + u % b | &0 <= u /\ u <= &1}`;;

let open_segment = new_definition
 `open_segment(a,b) = closed_segment[a,b] DIFF {a,b}`;;

let OPEN_SEGMENT_ALT = prove
 (`!a b:real^N.
        ~(a = b)
        ==> open_segment(a,b) = {(&1 - u) % a + u % b | &0 < u /\ u < &1}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[open_segment; closed_segment] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `u:real` THEN ASM_CASES_TAC `x:real^N = (&1 - u) % a + u % b` THEN
  ASM_REWRITE_TAC[REAL_LE_LT;
    VECTOR_ARITH `(&1 - u) % a + u % b = a <=> u % (b - a) = vec 0`;
    VECTOR_ARITH `(&1 - u) % a + u % b = b <=> (&1 - u) % (b - a) = vec 0`;
    VECTOR_MUL_EQ_0; REAL_SUB_0; VECTOR_SUB_EQ] THEN
  REAL_ARITH_TAC);;

make_overloadable "segment" `:A`;;

overload_interface("segment",`open_segment`);;
overload_interface("segment",`closed_segment`);;

let segment = prove
 (`segment[a,b] = {(&1 - u) % a + u % b | &0 <= u /\ u <= &1} /\
   segment(a,b) = segment[a,b] DIFF {a,b}`,
  REWRITE_TAC[open_segment; closed_segment]);;

let SEGMENT_REFL = prove
 (`(!a. segment[a,a] = {a}) /\
   (!a. segment(a,a) = {})`,
  REWRITE_TAC[segment; VECTOR_ARITH `(&1 - u) % a + u % a = a`] THEN
  SET_TAC[REAL_POS]);;

let IN_SEGMENT = prove
 (`!a b x:real^N.
        (x IN segment[a,b] <=>
         ?u. &0 <= u /\ u <= &1 /\ x = (&1 - u) % a + u % b) /\
        (x IN segment(a,b) <=>
         ~(a = b) /\ ?u. &0 < u /\ u < &1 /\ x = (&1 - u) % a + u % b)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[segment; IN_ELIM_THM; CONJ_ASSOC]; ALL_TAC] THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; NOT_IN_EMPTY] THEN
  ASM_SIMP_TAC[OPEN_SEGMENT_ALT; IN_ELIM_THM; CONJ_ASSOC]);;

let SEGMENT_SYM = prove
 (`(!a b:real^N. segment[a,b] = segment[b,a]) /\
   (!a b:real^N. segment(a,b) = segment(b,a))`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
  SIMP_TAC[open_segment] THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[INSERT_AC]] THEN
  REWRITE_TAC[EXTENSION; IN_SEGMENT] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `u:real`) THEN EXISTS_TAC `&1 - u` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN VECTOR_ARITH_TAC);;

let ENDS_IN_SEGMENT = prove
 (`!a b. a IN segment[a,b] /\ b IN segment[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[segment; IN_ELIM_THM] THENL
   [EXISTS_TAC `&0`; EXISTS_TAC `&1`] THEN
  (CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]));;

let ENDS_NOT_IN_SEGMENT = prove
 (`!a b. ~(a IN segment(a,b)) /\ ~(b IN segment(a,b))`,
  REWRITE_TAC[open_segment] THEN SET_TAC[]);;

let SEGMENT_CLOSED_OPEN = prove
 (`!a b. segment[a,b] = segment(a,b) UNION {a,b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[open_segment] THEN MATCH_MP_TAC(SET_RULE
   `a IN s /\ b IN s ==> s = (s DIFF {a,b}) UNION {a,b}`) THEN
  REWRITE_TAC[ENDS_IN_SEGMENT]);;

let MIDPOINT_IN_SEGMENT = prove
 (`(!a b:real^N. midpoint(a,b) IN segment[a,b]) /\
   (!a b:real^N. midpoint(a,b) IN segment(a,b) <=> ~(a = b))`,
  REWRITE_TAC[IN_SEGMENT] THEN REPEAT STRIP_TAC THENL
   [ALL_TAC; ASM_CASES_TAC `a:real^N = b` THEN ASM_REWRITE_TAC[]] THEN
  EXISTS_TAC `&1 / &2` THEN REWRITE_TAC[midpoint] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC);;

let BETWEEN_IN_SEGMENT = prove
 (`!x a b:real^N. between x (a,b) <=> x IN segment[a,b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[between] THEN
  ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; IN_SING] THENL [NORM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[segment; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(ASSUME_TAC o SYM) THEN
    EXISTS_TAC `dist(a:real^N,x) / dist(a,b)` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; DIST_POS_LT] THEN CONJ_TAC
    THENL [FIRST_ASSUM(SUBST1_TAC o SYM) THEN NORM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC `dist(a:real^N,b)` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; VECTOR_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
                 REAL_DIV_LMUL; DIST_EQ_0] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DIST_TRIANGLE_EQ] o SYM) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[dist; REAL_ARITH `(a + b) * &1 - a = b`] THEN
    VECTOR_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[dist] THEN
    REWRITE_TAC[VECTOR_ARITH `a - ((&1 - u) % a + u % b) = u % (a - b)`;
                VECTOR_ARITH `((&1 - u) % a + u % b) - b = (&1 - u) % (a - b)`;
                NORM_MUL; GSYM REAL_ADD_LDISTRIB] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD]);;

let IN_SEGMENT_COMPONENT = prove
 (`!a b x:real^N i.
        x IN segment[a,b] /\ 1 <= i /\ i <= dimindex(:N)
        ==> min (a$i) (b$i) <= x$i /\ x$i <= max (a$i) (b$i)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT]) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[REAL_ARITH `c <= u * a + t * b <=> u * --a + t * --b <= --c`] THEN
  MATCH_MP_TAC REAL_CONVEX_BOUND_LE THEN ASM_REAL_ARITH_TAC);;

let SEGMENT_1 = prove
 (`(!a b. segment[a,b] =
          if drop a <= drop b then interval[a,b] else interval[b,a]) /\
   (!a b. segment(a,b) =
          if drop a <= drop b then interval(a,b) else interval(b,a))`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[open_segment] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY;
              EXTENSION; GSYM BETWEEN_IN_SEGMENT; between; IN_INTERVAL_1] THEN
  REWRITE_TAC[GSYM DROP_EQ; DIST_REAL; GSYM drop] THEN ASM_REAL_ARITH_TAC);;

let OPEN_SEGMENT_1 = prove
 (`!a b:real^1. open(segment(a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEGMENT_1] THEN
  COND_CASES_TAC THEN REWRITE_TAC[OPEN_INTERVAL]);;

let SEGMENT_TRANSLATION = prove
 (`(!c a b. segment[c + a,c + b] = IMAGE (\x. c + x) (segment[a,b])) /\
   (!c a b. segment(c + a,c + b) = IMAGE (\x. c + x) (segment(a,b)))`,
  REWRITE_TAC[EXTENSION; IN_SEGMENT; IN_IMAGE] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - u) % (c + a) + u % (c + b) =
                            c + (&1 - u) % a + u % b`] THEN
  REWRITE_TAC[VECTOR_ARITH `c + a:real^N = c + b <=> a = b`] THEN
  MESON_TAC[]);;

add_translation_invariants
 [CONJUNCT1 SEGMENT_TRANSLATION; CONJUNCT2 SEGMENT_TRANSLATION];;

let CLOSED_SEGMENT_LINEAR_IMAGE = prove
 (`!f a b. linear f
           ==> segment[f a,f b] = IMAGE f (segment[a,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SEGMENT] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_CMUL th)]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_ADD th)]) THEN
  MESON_TAC[]);;

add_linear_invariants [CLOSED_SEGMENT_LINEAR_IMAGE];;

let OPEN_SEGMENT_LINEAR_IMAGE = prove
 (`!f:real^M->real^N a b.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> segment(f a,f b) = IMAGE f (segment(a,b))`,
  REWRITE_TAC[open_segment] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [OPEN_SEGMENT_LINEAR_IMAGE];;

let IN_OPEN_SEGMENT = prove
 (`!a b x:real^N.
        x IN segment(a,b) <=> x IN segment[a,b] /\ ~(x = a) /\ ~(x = b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[open_segment; IN_DIFF] THEN SET_TAC[]);;

let IN_OPEN_SEGMENT_ALT = prove
 (`!a b x:real^N.
        x IN segment(a,b) <=>
        x IN segment[a,b] /\ ~(x = a) /\ ~(x = b) /\ ~(a = b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = b` THEN
  ASM_REWRITE_TAC[SEGMENT_REFL; IN_SING; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[IN_OPEN_SEGMENT]);;

let COLLINEAR_DIST_IN_CLOSED_SEGMENT = prove
 (`!a b x. collinear {x,a,b} /\
           dist(x,a) <= dist(a,b) /\ dist(x,b) <= dist(a,b)
           ==> x IN segment[a,b]`,
  REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; COLLINEAR_DIST_BETWEEN]);;

let COLLINEAR_DIST_IN_OPEN_SEGMENT = prove
 (`!a b x. collinear {x,a,b} /\
           dist(x,a) < dist(a,b) /\ dist(x,b) < dist(a,b)
           ==> x IN segment(a,b)`,
  REWRITE_TAC[IN_OPEN_SEGMENT] THEN
  MESON_TAC[COLLINEAR_DIST_IN_CLOSED_SEGMENT; REAL_LT_LE; DIST_SYM]);;

let SEGMENT_SCALAR_MULTIPLE = prove
 (`(!a b v. segment[a % v,b % v] =
            {x % v:real^N | a <= x /\ x <= b \/ b <= x /\ x <= a}) /\
   (!a b v. ~(v = vec 0)
            ==> segment(a % v,b % v) =
                {x % v:real^N | a < x /\ x < b \/ b < x /\ x < a})`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN REPEAT STRIP_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(SPECL [`a % basis 1:real^1`; `b % basis 1:real^1`]
     (CONJUNCT1 SEGMENT_1)) THEN
    REWRITE_TAC[segment; VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB] THEN
    REWRITE_TAC[SET_RULE `{f x % b | p x} = IMAGE (\a. a % b) {f x | p x}`] THEN
    DISCH_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `IMAGE drop`) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF; DROP_CMUL] THEN
    SIMP_TAC[drop; BASIS_COMPONENT; DIMINDEX_GE_1; LE_REFL] THEN
    REWRITE_TAC[REAL_MUL_RID; IMAGE_ID] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    CONJ_TAC THENL [MESON_TAC[LIFT_DROP]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_LIFT; LIFT_DROP] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
    SIMP_TAC[drop; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_GE_1;
             LE_REFL; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[open_segment] THEN
    ASM_SIMP_TAC[VECTOR_MUL_RCANCEL; SET_RULE
     `(!x y. x % v = y % v <=> x = y)
      ==> {x % v | P x} DIFF {a % v,b % v} =
          {x % v | P x /\ ~(x = a) /\ ~(x = b)}`] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REAL_ARITH_TAC]);;

let FINITE_INTER_COLLINEAR_OPEN_SEGMENTS = prove
 (`!a b c d:real^N.
        collinear{a,b,c}
        ==> (FINITE(segment(a,b) INTER segment(c,d)) <=>
             segment(a,b) INTER segment(c,d) = {})`,
  REPEAT GEN_TAC THEN ABBREV_TAC `m:real^N = b - a` THEN POP_ASSUM MP_TAC THEN
  GEOM_NORMALIZE_TAC `m:real^N` THEN
  SIMP_TAC[VECTOR_SUB_EQ; SEGMENT_REFL; INTER_EMPTY; FINITE_EMPTY] THEN
  X_GEN_TAC `m:real^N` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN POP_ASSUM MP_TAC THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN GEOM_BASIS_MULTIPLE_TAC 1 `b:real^N` THEN
  X_GEN_TAC `b:real` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  SIMP_TAC[VECTOR_SUB_RZERO; NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
  ASM_REWRITE_TAC[real_abs; REAL_MUL_RID] THEN DISCH_THEN SUBST_ALL_TAC THEN
  POP_ASSUM(K ALL_TAC) THEN
  ASM_CASES_TAC `collinear{vec 0:real^N,&1 % basis 1,y}` THENL
   [POP_ASSUM MP_TAC THEN
    SIMP_TAC[COLLINEAR_LEMMA_ALT; BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN
    MATCH_MP_TAC(TAUT
     `~a /\ (b ==> c ==> d) ==> a \/ b ==> a \/ c ==> d`) THEN
    CONJ_TAC THENL
     [SIMP_TAC[VECTOR_MUL_LID; BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `b:real` THEN DISCH_THEN SUBST_ALL_TAC THEN
    X_GEN_TAC `a:real` THEN DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RID] THEN
    SUBST1_TAC(VECTOR_ARITH `vec 0:real^N = &0 % basis 1`) THEN
    SIMP_TAC[SEGMENT_SCALAR_MULTIPLE; BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL;
     VECTOR_MUL_RCANCEL; IMAGE_EQ_EMPTY; FINITE_IMAGE_INJ_EQ; SET_RULE
     `(!x y. x % v = y % v <=> x = y)
      ==> {x % v | P x} INTER {x % v | Q x} =
          IMAGE (\x. x % v) {x | P x /\ Q x}`] THEN
    REWRITE_TAC[REAL_ARITH `(&0 < x /\ x < &1 \/ &1 < x /\ x < &0) /\
                            (b < x /\ x < a \/ a < x /\ x < b) <=>
                       max (&0) (min a b) < x /\ x < min (&1) (max a b)`] THEN
    SIMP_TAC[FINITE_REAL_INTERVAL; EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    SIMP_TAC[GSYM REAL_LT_BETWEEN; GSYM NOT_EXISTS_THM] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN ASM_CASES_TAC
     `segment(vec 0:real^N,&1 % basis 1) INTER segment (x,y) = {}` THEN
    ASM_REWRITE_TAC[FINITE_EMPTY] THEN DISCH_THEN(K ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[open_segment; IN_DIFF; NOT_IN_EMPTY;
                DE_MORGAN_THM; IN_INTER; IN_INSERT] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~collinear{vec 0:real^N,&1 % basis 1, y}` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_MUL_LID]) THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN
    MATCH_MP_TAC COLLINEAR_SUBSET THEN
    EXISTS_TAC `{p,x:real^N, y, vec 0, basis 1}` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MP_TAC(ISPECL [`{y:real^N,vec 0,basis 1}`; `p:real^N`; `x:real^N`]
        COLLINEAR_TRIPLES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE `{p,x,y} = {x,p,y}`] THEN
      MATCH_MP_TAC BETWEEN_IMP_COLLINEAR THEN
      ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM COLLINEAR_4_3] THEN
    ONCE_REWRITE_TAC[SET_RULE `{p,x,z,w} = {w,z,p,x}`] THEN
    SIMP_TAC[COLLINEAR_4_3; BASIS_NONZERO; DIMINDEX_GE_1; ARITH] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP BETWEEN_IMP_COLLINEAR o
        GEN_REWRITE_RULE I [GSYM BETWEEN_IN_SEGMENT])) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN SIMP_TAC[INSERT_AC]]);;

let DIST_IN_CLOSED_SEGMENT,DIST_IN_OPEN_SEGMENT = (CONJ_PAIR o prove)
 (`(!a b x:real^N.
    x IN segment[a,b] ==> dist(x,a) <= dist(a,b) /\ dist(x,b) <= dist(a,b)) /\
   (!a b x:real^N.
    x IN segment(a,b) ==> dist(x,a) < dist(a,b) /\ dist(x,b) < dist(a,b))`,
  SIMP_TAC[IN_SEGMENT; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM; dist;
           VECTOR_ARITH
    `((&1 - u) % a + u % b) - a:real^N = u % (b - a) /\
     ((&1 - u) % a + u % b) - b = --(&1 - u) % (b - a)`] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_NEG; NORM_SUB] THEN CONJ_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [REWRITE_TAC[REAL_ARITH `x * y <= y <=> x * y <= &1 * y`] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `x * y < y <=> x * y < &1 * y`] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ; NORM_POS_LT; VECTOR_SUB_EQ] THEN
    ASM_REAL_ARITH_TAC]);;

let DIST_DECREASES_OPEN_SEGMENT = prove
 (`!a b c x:real^N.
      x IN segment(a,b) ==> dist(c,x) < dist(c,a) \/ dist(c,x) < dist(c,b)`,
  GEOM_ORIGIN_TAC `a:real^N` THEN GEOM_NORMALIZE_TAC `b:real^N` THEN
  REWRITE_TAC[SEGMENT_REFL; NOT_IN_EMPTY] THEN X_GEN_TAC `b:real^N` THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `b:real^N` THEN X_GEN_TAC `b:real` THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; real_abs; DIMINDEX_GE_1; LE_REFL;
           REAL_MUL_RID; VECTOR_MUL_LID] THEN
  REPEAT(DISCH_THEN(K ALL_TAC)) THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_SEGMENT; dist] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  SUBGOAL_THEN
   `norm((c$1 - u) % basis 1:real^N) < norm((c:real^N)$1 % basis 1:real^N) \/
    norm((c$1 - u) % basis 1:real^N) < norm((c$1 - &1) % basis 1:real^N)`
  MP_TAC THENL
   [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_GE_1; LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[NORM_LT; DOT_LMUL; DOT_RMUL; DOT_BASIS; DIMINDEX_GE_1;
              DOT_LSUB; DOT_RSUB; LE_REFL; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
              BASIS_COMPONENT; DOT_LZERO; DOT_RZERO; VECTOR_SUB_COMPONENT] THEN
    ASM_REAL_ARITH_TAC]);;

let DIST_DECREASES_CLOSED_SEGMENT = prove
 (`!a b c x:real^N.
      x IN segment[a,b] ==> dist(c,x) <= dist(c,a) \/ dist(c,x) <= dist(c,b)`,
  REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[DIST_DECREASES_OPEN_SEGMENT; REAL_LE_REFL; REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* Limit component bounds.                                                   *)
(* ------------------------------------------------------------------------- *)

let LIM_COMPONENT_UBOUND = prove
 (`!net:(A)net f (l:real^N) b k.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. (f x)$k <= b) net /\
        1 <= k /\ k <= dimindex(:N)
        ==> l$k <= b`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`net:(A)net`; `f:A->real^N`; `{y:real^N | basis k dot y <= b}`; `l:real^N`]
   LIM_IN_CLOSED_SET) THEN
  ASM_SIMP_TAC[CLOSED_HALFSPACE_LE; IN_ELIM_THM; DOT_BASIS]);;

let LIM_COMPONENT_LBOUND = prove
 (`!net:(A)net f (l:real^N) b k.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. b <= (f x)$k) net /\
        1 <= k /\ k <= dimindex(:N)
        ==> b <= l$k`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`net:(A)net`; `f:A->real^N`; `{y:real^N | b <= basis k dot y}`; `l:real^N`]
   LIM_IN_CLOSED_SET) THEN
  ASM_SIMP_TAC[REWRITE_RULE[real_ge] CLOSED_HALFSPACE_GE;
               IN_ELIM_THM; DOT_BASIS]);;

let LIM_COMPONENT_EQ = prove
 (`!net f:A->real^N i l b.
        (f --> l) net /\ 1 <= i /\ i <= dimindex(:N) /\
        ~(trivial_limit net) /\ eventually (\x. f(x)$i = b) net
        ==> l$i = b`,
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; EVENTUALLY_AND] THEN
  MESON_TAC[LIM_COMPONENT_UBOUND; LIM_COMPONENT_LBOUND]);;

let LIM_COMPONENT_LE = prove
 (`!net:(A)net f:A->real^N g:A->real^N k l m.
         ~(trivial_limit net) /\ (f --> l) net /\ (g --> m) net /\
        eventually (\x. (f x)$k <= (g x)$k) net /\
        1 <= k /\ k <= dimindex(:N)
        ==> l$k <= m$k`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT; LIM_COMPONENT_LBOUND] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> b /\ a ==> c ==> d`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; LIM_COMPONENT_LBOUND]);;

let LIM_DROP_LE = prove
 (`!net:(A)net f g l m.
         ~(trivial_limit net) /\ (f --> l) net /\ (g --> m) net /\
        eventually (\x. drop(f x) <= drop(g x)) net
        ==> drop l <= drop m`,
  REWRITE_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `net:(A)net` LIM_COMPONENT_LE) THEN
  MAP_EVERY EXISTS_TAC [`f:A->real^1`; `g:A->real^1`] THEN
  ASM_REWRITE_TAC[DIMINDEX_1; LE_REFL]);;

let LIM_DROP_UBOUND = prove
 (`!net f:A->real^1 l b.
        (f --> l) net /\
        ~(trivial_limit net) /\ eventually (\x. drop(f x) <= b) net
        ==> drop l <= b`,
  SIMP_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LIM_COMPONENT_UBOUND THEN
  REWRITE_TAC[LE_REFL; DIMINDEX_1] THEN ASM_MESON_TAC[]);;

let LIM_DROP_LBOUND = prove
 (`!net f:A->real^1 l b.
        (f --> l) net /\
        ~(trivial_limit net) /\ eventually (\x. b <= drop(f x)) net
        ==> b <= drop l`,
  SIMP_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LIM_COMPONENT_LBOUND THEN
  REWRITE_TAC[LE_REFL; DIMINDEX_1] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Also extending closed bounds to closures.                                 *)
(* ------------------------------------------------------------------------- *)

let IMAGE_CLOSURE_SUBSET = prove
 (`!f (s:real^N->bool) (t:real^M->bool).
      f continuous_on closure s /\ closed t /\ IMAGE f s SUBSET t
      ==> IMAGE f (closure s) SUBSET t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closure s SUBSET {x | (f:real^N->real^M) x IN t}` MP_TAC
  THENL [MATCH_MP_TAC SUBSET_TRANS; SET_TAC []]  THEN
  EXISTS_TAC `{x | x IN closure s /\ (f:real^N->real^M) x IN t}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC CLOSURE_MINIMAL; SET_TAC[]] THEN
  ASM_SIMP_TAC[CONTINUOUS_CLOSED_PREIMAGE; CLOSED_CLOSURE] THEN
  MP_TAC (ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]);;

let CLOSURE_IMAGE_CLOSURE = prove
 (`!f:real^M->real^N s.
        f continuous_on closure s
        ==> closure(IMAGE f (closure s)) = closure(IMAGE f s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  SIMP_TAC[SUBSET_CLOSURE; IMAGE_SUBSET; CLOSURE_SUBSET] THEN
  SIMP_TAC[CLOSURE_MINIMAL_EQ; CLOSED_CLOSURE] THEN
  MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
  ASM_REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET]);;

let CLOSURE_IMAGE_BOUNDED = prove
 (`!f:real^M->real^N s.
        f continuous_on closure s /\ bounded s
        ==> closure(IMAGE f s) = IMAGE f (closure s)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `closure(IMAGE (f:real^M->real^N) (closure s))` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CLOSURE_IMAGE_CLOSURE]; ALL_TAC] THEN
  MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  ASM_REWRITE_TAC[COMPACT_CLOSURE]);;

let CONTINUOUS_ON_CLOSURE_NORM_LE = prove
 (`!f:real^N->real^M s x b.
      f continuous_on (closure s) /\
      (!y. y IN s ==> norm(f y) <= b) /\
      x IN (closure s)
      ==> norm(f x) <= b`,
  REWRITE_TAC [GSYM IN_CBALL_0] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^M) (closure s) SUBSET cball(vec 0,b)`
    MP_TAC THENL
  [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET; ASM SET_TAC []] THEN
  ASM_REWRITE_TAC [CLOSED_CBALL] THEN ASM SET_TAC []);;

let CONTINUOUS_ON_CLOSURE_COMPONENT_LE = prove
 (`!f:real^N->real^M s x b k.
      f continuous_on (closure s) /\
      (!y. y IN s ==> (f y)$k <= b) /\
      x IN (closure s)
      ==> (f x)$k <= b`,
  REWRITE_TAC [GSYM IN_CBALL_0] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^M) (closure s) SUBSET {x | x$k <= b}`
  MP_TAC THENL
   [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET; ASM SET_TAC []] THEN
  ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE] THEN ASM SET_TAC[]);;

let CONTINUOUS_ON_CLOSURE_COMPONENT_GE = prove
 (`!f:real^N->real^M s x b k.
      f continuous_on (closure s) /\
      (!y. y IN s ==> b <= (f y)$k) /\
      x IN (closure s)
      ==> b <= (f x)$k`,
  REWRITE_TAC [GSYM IN_CBALL_0] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^M) (closure s) SUBSET {x | x$k >= b}`
  MP_TAC THENL
   [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET; ASM SET_TAC [real_ge]] THEN
  ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE] THEN ASM SET_TAC[real_ge]);;

(* ------------------------------------------------------------------------- *)
(* Limits relative to a union.                                               *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_UNION = prove
 (`(f --> l) (at x within (s UNION t)) <=>
   (f --> l) (at x within s) /\ (f --> l) (at x within t)`,
  REWRITE_TAC[LIM_WITHIN; IN_UNION; AND_FORALL_THM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_THEN
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `d:real`) (X_CHOOSE_TAC `k:real`)) THEN
  EXISTS_TAC `min d k` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  ASM_MESON_TAC[]);;

let CONTINUOUS_ON_UNION = prove
 (`!f s t. closed s /\ closed t /\ f continuous_on s /\ f continuous_on t
           ==> f continuous_on (s UNION t)`,
  REWRITE_TAC[CONTINUOUS_ON; CLOSED_LIMPT; IN_UNION; LIM_WITHIN_UNION] THEN
  MESON_TAC[LIM; TRIVIAL_LIMIT_WITHIN]);;

let CONTINUOUS_ON_CASES = prove
 (`!P f g:real^M->real^N s t.
        closed s /\ closed t /\ f continuous_on s /\ g continuous_on t /\
        (!x. x IN s /\ ~P x \/ x IN t /\ P x ==> f x = g x)
        ==> (\x. if P x then f x else g x) continuous_on (s UNION t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_UNION THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
   [EXISTS_TAC `f:real^M->real^N`; EXISTS_TAC `g:real^M->real^N`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let CONTINUOUS_ON_UNION_LOCAL = prove
 (`!f:real^M->real^N s.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        f continuous_on s /\ f continuous_on t
        ==> f continuous_on (s UNION t)`,
  REWRITE_TAC[CONTINUOUS_ON; CLOSED_IN_LIMPT; IN_UNION; LIM_WITHIN_UNION] THEN
  MESON_TAC[LIM; TRIVIAL_LIMIT_WITHIN]);;

let CONTINUOUS_ON_CASES_LOCAL = prove
 (`!P f g:real^M->real^N s t.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        f continuous_on s /\ g continuous_on t /\
        (!x. x IN s /\ ~P x \/ x IN t /\ P x ==> f x = g x)
        ==> (\x. if P x then f x else g x) continuous_on (s UNION t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
   [EXISTS_TAC `f:real^M->real^N`; EXISTS_TAC `g:real^M->real^N`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let CONTINUOUS_ON_CASES_LE = prove
 (`!f g:real^M->real^N h s a.
        f continuous_on {t | t IN s /\ h t <= a} /\
        g continuous_on {t | t IN s /\ a <= h t} /\
        (lift o h) continuous_on s /\
        (!t. t IN s /\ h t = a ==> f t = g t)
        ==> (\t. if h t <= a then f(t) else g(t)) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC
   `{t | t IN s /\ (h:real^M->real) t <= a} UNION
    {t | t IN s /\ a <= h t}` THEN
  CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[SUBSET; IN_UNION; IN_ELIM_THM; REAL_LE_TOTAL]] THEN
  MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC; REAL_LE_ANTISYM] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `{t | t IN s /\ (h:real^M->real) t <= a} =
      {t | t IN ({t | t IN s /\ h t <= a} UNION {t | t IN s /\ a <= h t}) /\
           (lift o h) t IN {x | x$1 <= a}}`
     (fun th -> GEN_REWRITE_TAC RAND_CONV [th])
    THENL
     [REWRITE_TAC[GSYM drop; o_THM; IN_ELIM_THM; LIFT_DROP; EXTENSION;
                  IN_UNION] THEN
      GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
      ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE; ETA_AX] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      SET_TAC[]];
    SUBGOAL_THEN
     `{t | t IN s /\ a <= (h:real^M->real) t} =
      {t | t IN ({t | t IN s /\ h t <= a} UNION {t | t IN s /\ a <= h t}) /\
           (lift o h) t IN {x | x$1 >= a}}`
     (fun th -> GEN_REWRITE_TAC RAND_CONV [th])
    THENL
     [REWRITE_TAC[GSYM drop; o_THM; IN_ELIM_THM; LIFT_DROP; EXTENSION;
                  IN_UNION] THEN
      GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN
      ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE; ETA_AX] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      SET_TAC[]]]);;

let CONTINUOUS_ON_CASES_1 = prove
 (`!f g:real^1->real^N s a.
        f continuous_on {t | t IN s /\ drop t <= a} /\
        g continuous_on {t | t IN s /\ a <= drop t} /\
        (lift a IN s ==> f(lift a) = g(lift a))
        ==> (\t. if drop t <= a then f(t) else g(t)) continuous_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LE THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID] THEN
  REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP] THEN ASM_MESON_TAC[]);;

let EXTENSION_FROM_CLOPEN = prove
 (`!f:real^M->real^N s t u.
        open_in (subtopology euclidean s) t /\
        closed_in (subtopology euclidean s) t /\
        f continuous_on t /\ IMAGE f t SUBSET u /\ (u = {} ==> s = {})
        ==> ?g. g continuous_on s /\ IMAGE g s SUBSET u /\
                !x. x IN t ==> g x = f x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `u:real^N->bool = {}` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_EMPTY; IMAGE_CLAUSES; SUBSET_EMPTY;
               IMAGE_EQ_EMPTY; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  EXISTS_TAC `\x. if x IN t then (f:real^M->real^N) x else a` THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN
  SUBGOAL_THEN `s:real^M->bool = t UNION (s DIFF t)` SUBST1_TAC THENL
   [ASM SET_TAC[]; MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL] THEN
  ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> t UNION (s DIFF t) = s`] THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST; IN_DIFF] THEN
  CONJ_TAC THENL [MATCH_MP_TAC CLOSED_IN_DIFF; MESON_TAC[]] THEN
  ASM_REWRITE_TAC[CLOSED_IN_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Componentwise limits and continuity.                                      *)
(* ------------------------------------------------------------------------- *)

let LIM_COMPONENTWISE_LIFT = prove
 (`!net f:A->real^N.
        (f --> l) net <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> ((\x. lift((f x)$i)) --> lift(l$i)) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tendsto] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    GEN_TAC THEN REWRITE_TAC[dist] THEN MATCH_MP_TAC(REAL_ARITH
     `y <= x ==> x < e ==> y < e`) THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM; GSYM LIFT_SUB; NORM_LIFT;
                 GSYM VECTOR_SUB_COMPONENT];
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_FORALL_THM] THEN
    ONCE_REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; RIGHT_FORALL_IMP_THM] THEN
    SIMP_TAC[FORALL_EVENTUALLY; FINITE_NUMSEG; NUMSEG_EMPTY;
             GSYM NOT_LE; DIMINDEX_GE_1] THEN
    REWRITE_TAC[DIST_LIFT; GSYM VECTOR_SUB_COMPONENT] THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &(dimindex(:N))`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `x:A` THEN SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; dist] THEN
    DISCH_TAC THEN W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC(REAL_ARITH `s < e ==> n <= s ==> n < e`) THEN
    MATCH_MP_TAC SUM_BOUND_LT_GEN THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1;
                 CARD_NUMSEG_1; GSYM IN_NUMSEG]]);;

let CONTINUOUS_COMPONENTWISE_LIFT = prove
 (`!net f:A->real^N.
        f continuous net <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift((f x)$i)) continuous net`,
  REWRITE_TAC[continuous; GSYM LIM_COMPONENTWISE_LIFT]);;

let CONTINUOUS_ON_COMPONENTWISE_LIFT = prove
 (`!f:real^M->real^N s.
        f continuous_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift((f x)$i)) continuous_on s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [CONTINUOUS_COMPONENTWISE_LIFT] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some more convenient intermediate-value theorem formulations.             *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_IVT_HYPERPLANE = prove
 (`!s x y:real^N a b.
        connected s /\
        x IN s /\ y IN s /\ a dot x <= b /\ b <= a dot y
        ==> ?z. z IN s /\ a dot z = b`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPECL
   [`{x:real^N | a dot x < b}`; `{x:real^N | a dot x > b}`]) THEN
  REWRITE_TAC[OPEN_HALFSPACE_LT; OPEN_HALFSPACE_GT] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY; SUBSET;
              IN_UNION; REAL_LT_LE; real_gt] THEN
  ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LE_ANTISYM]);;

let CONNECTED_IVT_COMPONENT = prove
 (`!s x y:real^N a k.
        connected s /\ x IN s /\ y IN s /\
        1 <= k /\ k <= dimindex(:N) /\ x$k <= a /\ a <= y$k
        ==> ?z. z IN s /\ z$k = a`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`s:real^N->bool`; `x:real^N`; `y:real^N`; `(basis k):real^N`;
    `a:real`] CONNECTED_IVT_HYPERPLANE) THEN
  ASM_SIMP_TAC[DOT_BASIS]);;

(* ------------------------------------------------------------------------- *)
(* Rather trivial observation that we can map any connected set on segment.  *)
(* ------------------------------------------------------------------------- *)

let MAPPING_CONNECTED_ONTO_SEGMENT = prove
 (`!s:real^M->bool a b:real^N.
        connected s /\ ~(?a. s SUBSET {a})
        ==> ?f. f continuous_on s /\ IMAGE f s = segment[a,b]`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `~(?a. s SUBSET {a}) ==> ?a b. a IN s /\ b IN s /\ ~(a = b)`)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN STRIP_TAC THEN EXISTS_TAC
   `\x:real^M. a + dist(u,x) / (dist(u,x) + dist(v,x)) % (b - a:real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN SIMP_TAC[o_DEF; CONTINUOUS_ON_CONST];
    REWRITE_TAC[segment; VECTOR_ARITH
     `(&1 - u) % a + u % b:real^N = a + u % (b - a)`] THEN
    MATCH_MP_TAC(SET_RULE
     `IMAGE f s = {x | P x}
      ==> IMAGE (\x. a + f x % b) s = {a + u % b:real^N | P u}`) THEN
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ;
      NORM_ARITH `~(u:real^N = v) ==> &0 < dist(u,x) + dist(v,x)`] THEN
    CONJ_TAC THENL [CONV_TAC NORM_ARITH; REWRITE_TAC[IN_IMAGE]] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`IMAGE (\x:real^M. lift(dist(u,x) / (dist(u,x) + dist(v,x)))) s`;
      `vec 0:real^1`; `vec 1:real^1`; `t:real`; `1`]
        CONNECTED_IVT_COMPONENT) THEN
    ASM_SIMP_TAC[VEC_COMPONENT; DIMINDEX_1; ARITH_LE] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE; GSYM drop; LIFT_DROP] THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_IMAGE]; MESON_TAC[]] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `u:real^M` THEN ASM_REWRITE_TAC[DIST_REFL; real_div] THEN
      REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN REAL_ARITH_TAC;
      EXISTS_TAC `v:real^M` THEN ASM_REWRITE_TAC[DIST_REFL] THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; DIST_EQ_0; REAL_ADD_RID] THEN
      REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ]]] THEN
  REWRITE_TAC[real_div; LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  REWRITE_TAC[CONTINUOUS_ON_LIFT_DIST] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN
  ASM_SIMP_TAC[LIFT_ADD; NORM_ARITH
   `~(u:real^N = v) ==> ~(dist(u,x) + dist(v,x) = &0)`] THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_ON_LIFT_DIST]);;

(* ------------------------------------------------------------------------- *)
(* Also more convenient formulations of monotone convergence.                *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_INCREASING_CONVERGENT = prove
 (`!s:num->real^1.
        bounded {s n | n IN (:num)} /\ (!n. drop(s n) <= drop(s(SUC n)))
        ==> ?l. (s --> l) sequentially`,
  GEN_TAC THEN
  REWRITE_TAC[bounded; IN_ELIM_THM; ABS_DROP; LIM_SEQUENTIALLY; dist;
              DROP_SUB; IN_UNIV; GSYM EXISTS_DROP] THEN
  DISCH_TAC THEN MATCH_MP_TAC CONVERGENT_BOUNDED_MONOTONE THEN
  REWRITE_TAC[LEFT_EXISTS_AND_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISJ1_TAC THEN MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
  ASM_REWRITE_TAC[REAL_LE_TRANS; REAL_LE_REFL]);;

let BOUNDED_DECREASING_CONVERGENT = prove
 (`!s:num->real^1.
        bounded {s n | n IN (:num)} /\ (!n. drop(s(SUC n)) <= drop(s(n)))
        ==> ?l. (s --> l) sequentially`,
  GEN_TAC THEN REWRITE_TAC[bounded; FORALL_IN_GSPEC] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPEC `\n. --((s:num->real^1) n)` BOUNDED_INCREASING_CONVERGENT) THEN
  ASM_SIMP_TAC[bounded; FORALL_IN_GSPEC; NORM_NEG; DROP_NEG; REAL_LE_NEG2] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [GSYM LIM_NEG_EQ] THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Since we'll use some cardinality reasoning, add invariance theorems.      *)
(* ------------------------------------------------------------------------- *)

let card_translation_invariants = (CONJUNCTS o prove)
 (`(!a (s:real^N->bool) (t:A->bool).
     IMAGE (\x. a + x) s =_c t <=> s =_c t) /\
   (!a (s:A->bool) (t:real^N->bool).
     s =_c IMAGE (\x. a + x) t <=> s =_c t) /\
   (!a (s:real^N->bool) (t:A->bool).
     IMAGE (\x. a + x) s <_c t <=> s <_c t) /\
   (!a (s:A->bool) (t:real^N->bool).
     s <_c IMAGE (\x. a + x) t <=> s <_c t) /\
   (!a (s:real^N->bool) (t:A->bool).
     IMAGE (\x. a + x) s <=_c t <=> s <=_c t) /\
   (!a (s:A->bool) (t:real^N->bool).
     s <=_c IMAGE (\x. a + x) t <=> s <=_c t) /\
   (!a (s:real^N->bool) (t:A->bool).
     IMAGE (\x. a + x) s >_c t <=> s >_c t) /\
   (!a (s:A->bool) (t:real^N->bool).
     s >_c IMAGE (\x. a + x) t <=> s >_c t) /\
   (!a (s:real^N->bool) (t:A->bool).
     IMAGE (\x. a + x) s >=_c t <=> s >=_c t) /\
   (!a (s:A->bool) (t:real^N->bool).
     s >=_c IMAGE (\x. a + x) t <=> s >=_c t)`,
  REWRITE_TAC[gt_c; ge_c] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CARD_EQ_CONG;
    MATCH_MP_TAC CARD_EQ_CONG;
    MATCH_MP_TAC CARD_LT_CONG;
    MATCH_MP_TAC CARD_LT_CONG;
    MATCH_MP_TAC CARD_LE_CONG;
    MATCH_MP_TAC CARD_LE_CONG;
    MATCH_MP_TAC CARD_LT_CONG;
    MATCH_MP_TAC CARD_LT_CONG;
    MATCH_MP_TAC CARD_LE_CONG;
    MATCH_MP_TAC CARD_LE_CONG] THEN
  REWRITE_TAC[CARD_EQ_REFL] THEN MATCH_MP_TAC CARD_EQ_IMAGE THEN
  SIMP_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`]) in
add_translation_invariants card_translation_invariants;;

let card_linear_invariants = (CONJUNCTS o prove)
 (`(!(f:real^M->real^N) s (t:A->bool).
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (IMAGE f s =_c t <=> s =_c t)) /\
   (!(f:real^M->real^N) (s:A->bool) t.
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (s =_c IMAGE f t <=> s =_c t)) /\
   (!(f:real^M->real^N) s (t:A->bool).
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (IMAGE f s <_c t <=> s <_c t)) /\
   (!(f:real^M->real^N) (s:A->bool) t.
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (s <_c IMAGE f t <=> s <_c t)) /\
   (!(f:real^M->real^N) s (t:A->bool).
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (IMAGE f s <=_c t <=> s <=_c t)) /\
   (!(f:real^M->real^N) (s:A->bool) t.
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (s <=_c IMAGE f t <=> s <=_c t)) /\
   (!(f:real^M->real^N) s (t:A->bool).
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (IMAGE f s >_c t <=> s >_c t)) /\
   (!(f:real^M->real^N) (s:A->bool) t.
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (s >_c IMAGE f t <=> s >_c t)) /\
   (!(f:real^M->real^N) s (t:A->bool).
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (IMAGE f s >=_c t <=> s >=_c t)) /\
   (!(f:real^M->real^N) (s:A->bool) t.
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (s >=_c IMAGE f t <=> s >=_c t))`,
  REWRITE_TAC[gt_c; ge_c] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CARD_EQ_CONG;
    MATCH_MP_TAC CARD_EQ_CONG;
    MATCH_MP_TAC CARD_LT_CONG;
    MATCH_MP_TAC CARD_LT_CONG;
    MATCH_MP_TAC CARD_LE_CONG;
    MATCH_MP_TAC CARD_LE_CONG;
    MATCH_MP_TAC CARD_LT_CONG;
    MATCH_MP_TAC CARD_LT_CONG;
    MATCH_MP_TAC CARD_LE_CONG;
    MATCH_MP_TAC CARD_LE_CONG] THEN
  REWRITE_TAC[CARD_EQ_REFL] THEN MATCH_MP_TAC CARD_EQ_IMAGE THEN
  ASM_MESON_TAC[]) in
add_linear_invariants card_linear_invariants;;

(* ------------------------------------------------------------------------- *)
(* Basic homeomorphism definitions.                                          *)
(* ------------------------------------------------------------------------- *)

let homeomorphism = new_definition
  `homeomorphism (s,t) (f,g) <=>
     (!x. x IN s ==> (g(f(x)) = x)) /\ (IMAGE f s = t) /\ f continuous_on s /\
     (!y. y IN t ==> (f(g(y)) = y)) /\ (IMAGE g t = s) /\ g continuous_on t`;;

parse_as_infix("homeomorphic",(12,"right"));;

let homeomorphic = new_definition
  `s homeomorphic t <=> ?f g. homeomorphism (s,t) (f,g)`;;

let HOMEOMORPHISM = prove
 (`!s:real^M->bool t:real^N->bool f g.
        homeomorphism (s,t) (f,g) <=>
         f continuous_on s /\ IMAGE f s SUBSET t /\
         g continuous_on t /\ IMAGE g t SUBSET s /\
         (!x. x IN s ==> g (f x) = x) /\
         (!y. y IN t ==> f (g y) = y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN
  EQ_TAC THEN SIMP_TAC[] THEN SET_TAC[]);;

let HOMEOMORPHISM_OF_SUBSETS = prove
 (`!f g s t s' t'.
    homeomorphism (s,t) (f,g) /\ s' SUBSET s /\ t' SUBSET t /\ IMAGE f s' = t'
    ==> homeomorphism (s',t') (f,g)`,
  REWRITE_TAC[homeomorphism] THEN
  REPEAT STRIP_TAC THEN
  TRY(MATCH_MP_TAC CONTINUOUS_ON_SUBSET) THEN ASM SET_TAC[]);;

let HOMEOMORPHISM_ID = prove
 (`!s:real^N->bool. homeomorphism (s,s) ((\x. x),(\x. x))`,
  REWRITE_TAC[homeomorphism; IMAGE_ID; CONTINUOUS_ON_ID]);;

let HOMEOMORPHISM_I = prove
 (`!s:real^N->bool. homeomorphism (s,s) (I,I)`,
  REWRITE_TAC[I_DEF; HOMEOMORPHISM_ID]);;

let HOMEOMORPHIC_REFL = prove
 (`!s:real^N->bool. s homeomorphic s`,
  REWRITE_TAC[homeomorphic] THEN MESON_TAC[HOMEOMORPHISM_I]);;

let HOMEOMORPHISM_SYM = prove
 (`!f:real^M->real^N g s t.
        homeomorphism (s,t) (f,g) <=> homeomorphism (t,s) (g,f)`,
  REWRITE_TAC[homeomorphism] THEN MESON_TAC[]);;

let HOMEOMORPHIC_SYM = prove
 (`!s t. s homeomorphic t <=> t homeomorphic s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic; homeomorphism] THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN CONV_TAC TAUT);;

let HOMEOMORPHISM_COMPOSE = prove
 (`!f:real^M->real^N g h:real^N->real^P k s t u.
        homeomorphism (s,t) (f,g) /\ homeomorphism (t,u) (h,k)
        ==> homeomorphism (s,u) (h o f,g o k)`,
  SIMP_TAC[homeomorphism; CONTINUOUS_ON_COMPOSE; IMAGE_o; o_THM] THEN
  SET_TAC[]);;

let HOMEOMORPHIC_TRANS = prove
 (`!s:real^M->bool t:real^N->bool u:real^P->bool.
        s homeomorphic t /\ t homeomorphic u ==> s homeomorphic u`,
  REWRITE_TAC[homeomorphic] THEN MESON_TAC[HOMEOMORPHISM_COMPOSE]);;

let HOMEOMORPHIC_IMP_CARD_EQ = prove
 (`!s:real^M->bool t:real^N->bool. s homeomorphic t ==> s =_c t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic; homeomorphism; eq_c] THEN
  MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]);;

let HOMEOMORPHIC_EMPTY = prove
 (`(!s. (s:real^N->bool) homeomorphic ({}:real^M->bool) <=> s = {}) /\
   (!s. ({}:real^M->bool) homeomorphic (s:real^N->bool) <=> s = {})`,
  REWRITE_TAC[homeomorphic; homeomorphism; IMAGE_CLAUSES; IMAGE_EQ_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[continuous_on; NOT_IN_EMPTY]);;

let HOMEOMORPHIC_MINIMAL = prove
 (`!s t. s homeomorphic t <=>
            ?f g. (!x. x IN s ==> f(x) IN t /\ (g(f(x)) = x)) /\
                  (!y. y IN t ==> g(y) IN s /\ (f(g(y)) = y)) /\
                  f continuous_on s /\ g continuous_on t`,
  REWRITE_TAC[homeomorphic; homeomorphism; EXTENSION; IN_IMAGE] THEN
  REPEAT GEN_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN MESON_TAC[]);;

let HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (IMAGE f s) homeomorphic s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_LEFT_INVERSE]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; FORALL_IN_IMAGE; FUN_IN_IMAGE] THEN
  ASM_SIMP_TAC[continuous_on; IMP_CONJ; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_BOUNDED_BELOW_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e * B:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  X_GEN_TAC `y:real^M` THEN ASM_SIMP_TAC[dist; GSYM LINEAR_SUB] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b < x ==> a < x`) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ]);;

let HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((IMAGE f s) homeomorphic t <=> s homeomorphic t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o SPEC `s:real^M->bool` o
    MATCH_MP HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_SELF) THEN
  EQ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_SYM]);
    POP_ASSUM MP_TAC] THEN
  REWRITE_TAC[IMP_IMP; HOMEOMORPHIC_TRANS]);;

let HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_RIGHT_EQ = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (s homeomorphic (IMAGE f t) <=> s homeomorphic t)`,
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  REWRITE_TAC[HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ]);;

add_linear_invariants
  [HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ;
   HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_RIGHT_EQ];;

let HOMEOMORPHIC_TRANSLATION_SELF = prove
 (`!a:real^N s. (IMAGE (\x. a + x) s) homeomorphic s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  EXISTS_TAC `\x:real^N. x - a` THEN
  EXISTS_TAC `\x:real^N. a + x` THEN
  SIMP_TAC[FORALL_IN_IMAGE; CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID;
           CONTINUOUS_ON_CONST; CONTINUOUS_ON_ADD; VECTOR_ADD_SUB] THEN
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

let HOMEOMORPHIC_TRANSLATION_LEFT_EQ = prove
 (`!a:real^N s t.
      (IMAGE (\x. a + x) s) homeomorphic t <=> s homeomorphic t`,
  MESON_TAC[HOMEOMORPHIC_TRANSLATION_SELF;
            HOMEOMORPHIC_SYM; HOMEOMORPHIC_TRANS]);;

let HOMEOMORPHIC_TRANSLATION_RIGHT_EQ = prove
 (`!a:real^N s t.
      s homeomorphic (IMAGE (\x. a + x) t) <=> s homeomorphic t`,
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  REWRITE_TAC[HOMEOMORPHIC_TRANSLATION_LEFT_EQ]);;

add_translation_invariants
  [HOMEOMORPHIC_TRANSLATION_LEFT_EQ;
   HOMEOMORPHIC_TRANSLATION_RIGHT_EQ];;

let HOMEOMORPHISM_IMP_QUOTIENT_MAP = prove
 (`!f:real^M->real^N g s t.
    homeomorphism (s,t) (f,g)
    ==> !u. u SUBSET t
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ f x IN u} <=>
                 open_in (subtopology euclidean t) u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN
  STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_RIGHT_INVERSE_IMP_QUOTIENT_MAP THEN
  EXISTS_TAC `g:real^N->real^M` THEN ASM_REWRITE_TAC[SUBSET_REFL]);;

let HOMEOMORPHIC_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool s':real^P->bool t':real^Q->bool.
        s homeomorphic s' /\ t homeomorphic t'
        ==> (s PCROSS t) homeomorphic (s' PCROSS t')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic; HOMEOMORPHISM] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `f:real^M->real^P`
     (X_CHOOSE_THEN `f':real^P->real^M` STRIP_ASSUME_TAC))
   (X_CHOOSE_THEN `g:real^N->real^Q`
     (X_CHOOSE_THEN `g':real^Q->real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`(\z. pastecart (f(fstcart z)) (g(sndcart z)))
     :real^(M,N)finite_sum->real^(P,Q)finite_sum`;
    `(\z. pastecart (f'(fstcart z)) (g'(sndcart z)))
     :real^(P,Q)finite_sum->real^(M,N)finite_sum`] THEN
  ASM_SIMP_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
               SUBSET; FORALL_IN_IMAGE; PASTECART_IN_PCROSS] THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_PASTECART THEN
  CONJ_TAC THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_FSTCART; LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_PCROSS; SUBSET] THEN
  SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART]);;

let HOMEOMORPHIC_PCROSS_SYM = prove
 (`!s:real^M->bool t:real^N->bool. (s PCROSS t) homeomorphic (t PCROSS s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic; homeomorphism] THEN
  EXISTS_TAC `(\z. pastecart (sndcart z) (fstcart z))
              :real^(M,N)finite_sum->real^(N,M)finite_sum` THEN
  EXISTS_TAC `(\z. pastecart (sndcart z) (fstcart z))
              :real^(N,M)finite_sum->real^(M,N)finite_sum` THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
  SIMP_TAC[CONTINUOUS_ON_PASTECART; LINEAR_CONTINUOUS_ON;
           LINEAR_FSTCART; LINEAR_SNDCART] THEN
  REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
    IN_IMAGE; EXISTS_PASTECART; PASTECART_INJ; PASTECART_IN_PCROSS] THEN
  MESON_TAC[]);;

let HOMEOMORPHIC_PCROSS_ASSOC = prove
 (`!s:real^M->bool t:real^N->bool u:real^P->bool.
        (s PCROSS (t PCROSS u)) homeomorphic ((s PCROSS t) PCROSS u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic; HOMEOMORPHISM] THEN
  MAP_EVERY EXISTS_TAC
   [`\z:real^(M,(N,P)finite_sum)finite_sum.
        pastecart (pastecart (fstcart z) (fstcart(sndcart z)))
                  (sndcart(sndcart z))`;
    `\z:real^((M,N)finite_sum,P)finite_sum.
        pastecart (fstcart(fstcart z))
                  (pastecart (sndcart(fstcart z)) (sndcart z))`] THEN
  REWRITE_TAC[FORALL_IN_PCROSS; SUBSET; FORALL_IN_IMAGE;
              RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_IN_PCROSS] THEN
  CONJ_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REPEAT(MATCH_MP_TAC LINEAR_PASTECART THEN CONJ_TAC) THEN
  TRY(GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC LINEAR_COMPOSE) THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]);;

let HOMEOMORPHIC_SCALING_LEFT = prove
 (`!c. &0 < c
       ==> !s t. (IMAGE (\x. c % x) s) homeomorphic t <=> s homeomorphic t`,
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_LEFT_EQ THEN
  ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ; LINEAR_SCALING]);;

let HOMEOMORPHIC_SCALING_RIGHT = prove
 (`!c. &0 < c
       ==> !s t. s homeomorphic (IMAGE (\x. c % x) t) <=> s homeomorphic t`,
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HOMEOMORPHIC_INJECTIVE_LINEAR_IMAGE_RIGHT_EQ THEN
  ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ; LINEAR_SCALING]);;

let HOMEOMORPHIC_SUBSPACES = prove
 (`!s:real^M->bool t:real^N->bool.
        subspace s /\ subspace t /\ dim s = dim t ==> s homeomorphic t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic; HOMEOMORPHISM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ISOMETRIES_SUBSPACES) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^M->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^M` THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_CBALL_0] THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN ASM SET_TAC[]);;

let HOMEOMORPHIC_FINITE = prove
 (`!s:real^M->bool t:real^N->bool.
        FINITE s /\ FINITE t ==> (s homeomorphic t <=> CARD s = CARD t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CARD_EQ) THEN
    ASM_SIMP_TAC[CARD_EQ_CARD];
    STRIP_TAC THEN REWRITE_TAC[homeomorphic; HOMEOMORPHISM] THEN
    MP_TAC(ISPECL [`s:real^M->bool`; `t:real^N->bool`]
        CARD_EQ_BIJECTIONS) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_FINITE] THEN ASM SET_TAC[]]);;

let HOMEOMORPHIC_FINITE_STRONG = prove
 (`!s:real^M->bool t:real^N->bool.
        FINITE s \/ FINITE t
        ==> (s homeomorphic t <=> FINITE s /\ FINITE t /\ CARD s = CARD t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN EQ_TAC THEN
  SIMP_TAC[HOMEOMORPHIC_FINITE] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CARD_FINITE_CONG o MATCH_MP
    HOMEOMORPHIC_IMP_CARD_EQ) THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[HOMEOMORPHIC_FINITE]);;

let HOMEOMORPHIC_SING = prove
 (`!a:real^M b:real^N. {a} homeomorphic {b}`,
  SIMP_TAC[HOMEOMORPHIC_FINITE; FINITE_SING; CARD_SING]);;

let HOMEOMORPHIC_PCROSS_SING = prove
 (`(!s:real^M->bool a:real^N. s homeomorphic (s PCROSS {a})) /\
   (!s:real^M->bool a:real^N. s homeomorphic ({a} PCROSS s))`,
  MATCH_MP_TAC(TAUT `(p ==> q) /\ p ==> p /\ q`) THEN CONJ_TAC THENL
   [MESON_TAC[HOMEOMORPHIC_PCROSS_SYM; HOMEOMORPHIC_TRANS]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic; HOMEOMORPHISM] THEN
  EXISTS_TAC `\x. (pastecart x a:real^(M,N)finite_sum)` THEN
  EXISTS_TAC `fstcart:real^(M,N)finite_sum->real^M` THEN
  SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
  SIMP_TAC[LINEAR_FSTCART; LINEAR_CONTINUOUS_ON; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[FORALL_IN_PCROSS; PASTECART_IN_PCROSS; IN_SING] THEN
  SIMP_TAC[FSTCART_PASTECART]);;

(* ------------------------------------------------------------------------- *)
(* Inverse function property for open/closed maps.                           *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_INVERSE_OPEN_MAP = prove
 (`!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s = t /\ (!x. x IN s ==> g(f x) = x) /\
        (!u. open_in (subtopology euclidean s) u
             ==> open_in (subtopology euclidean t) (IMAGE f u))
        ==> g continuous_on t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^N->real^M`; `t:real^N->bool`; `s:real^M->bool`]
        CONTINUOUS_ON_OPEN_GEN) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  X_GEN_TAC `u:real^M->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
  ASM SET_TAC[]);;

let CONTINUOUS_ON_INVERSE_CLOSED_MAP = prove
 (`!f:real^M->real^N g s t.
        f continuous_on s /\ IMAGE f s = t /\ (!x. x IN s ==> g(f x) = x) /\
        (!u. closed_in (subtopology euclidean s) u
             ==> closed_in (subtopology euclidean t) (IMAGE f u))
        ==> g continuous_on t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^N->real^M`; `t:real^N->bool`; `s:real^M->bool`]
        CONTINUOUS_ON_CLOSED_GEN) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  X_GEN_TAC `u:real^M->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [closed_in]) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[]);;

let HOMEOMORPHISM_INJECTIVE_OPEN_MAP = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        (!u. open_in (subtopology euclidean s) u
             ==> open_in (subtopology euclidean t) (IMAGE f u))
        ==> ?g. homeomorphism (s,t) (f,g)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^M` THEN
  DISCH_TAC THEN ASM_SIMP_TAC[homeomorphism] THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  MATCH_MP_TAC CONTINUOUS_ON_INVERSE_OPEN_MAP THEN ASM_MESON_TAC[]);;

let HOMEOMORPHISM_INJECTIVE_CLOSED_MAP = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        (!u. closed_in (subtopology euclidean s) u
             ==> closed_in (subtopology euclidean t) (IMAGE f u))
        ==> ?g. homeomorphism (s,t) (f,g)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^M` THEN
  DISCH_TAC THEN ASM_SIMP_TAC[homeomorphism] THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  MATCH_MP_TAC CONTINUOUS_ON_INVERSE_CLOSED_MAP THEN ASM_MESON_TAC[]);;

let HOMEOMORPHISM_IMP_OPEN_MAP = prove
 (`!f:real^M->real^N g s t u.
        homeomorphism (s,t) (f,g) /\ open_in (subtopology euclidean s) u
        ==> open_in (subtopology euclidean t) (IMAGE f u)`,
  REWRITE_TAC[homeomorphism] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) u =
                 {y | y IN t /\ g(y) IN u}`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [open_in]) THEN
    ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_IMP_OPEN_IN THEN ASM_REWRITE_TAC[]]);;

let HOMEOMORPHISM_IMP_CLOSED_MAP = prove
 (`!f:real^M->real^N g s t u.
        homeomorphism (s,t) (f,g) /\ closed_in (subtopology euclidean s) u
        ==> closed_in (subtopology euclidean t) (IMAGE f u)`,
  REWRITE_TAC[homeomorphism] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) u =
                 {y | y IN t /\ g(y) IN u}`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [closed_in]) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN ASM SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_IMP_CLOSED_IN THEN ASM_REWRITE_TAC[]]);;

let HOMEOMORPHISM_INJECTIVE_OPEN_MAP_EQ = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ((?g. homeomorphism (s,t) (f,g)) <=>
             !u. open_in (subtopology euclidean s) u
                 ==> open_in (subtopology euclidean t) (IMAGE f u))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN ASM_MESON_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_INJECTIVE_OPEN_MAP THEN
    ASM_REWRITE_TAC[]]);;

let HOMEOMORPHISM_INJECTIVE_CLOSED_MAP_EQ = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ((?g. homeomorphism (s,t) (f,g)) <=>
             !u. closed_in (subtopology euclidean s) u
                 ==> closed_in (subtopology euclidean t) (IMAGE f u))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_CLOSED_MAP THEN ASM_MESON_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_INJECTIVE_CLOSED_MAP THEN
    ASM_REWRITE_TAC[]]);;

let INJECTIVE_MAP_OPEN_IFF_CLOSED = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ((!u. open_in (subtopology euclidean s) u
                  ==> open_in (subtopology euclidean t) (IMAGE f u)) <=>
             (!u. closed_in (subtopology euclidean s) u
                  ==> closed_in (subtopology euclidean t) (IMAGE f u)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `?g:real^N->real^M. homeomorphism (s,t) (f,g)` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC HOMEOMORPHISM_INJECTIVE_OPEN_MAP_EQ;
    MATCH_MP_TAC HOMEOMORPHISM_INJECTIVE_CLOSED_MAP_EQ] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Relatively weak hypotheses if the domain of the function is compact.      *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_IMP_CLOSED_MAP = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\ compact s
        ==> !u. closed_in (subtopology euclidean s) u
                ==> closed_in (subtopology euclidean t) (IMAGE f u)`,
  SIMP_TAC[CLOSED_IN_CLOSED_EQ; COMPACT_IMP_CLOSED] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_SUBSET THEN
  EXPAND_TAC "t" THEN ASM_SIMP_TAC[IMAGE_SUBSET] THEN
  MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_IN_CLOSED_TRANS;
                BOUNDED_SUBSET; CONTINUOUS_ON_SUBSET]);;

let CONTINUOUS_IMP_QUOTIENT_MAP = prove
 (`!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s = t /\ compact s
        ==> !u. u SUBSET t
                ==> (open_in (subtopology euclidean s)
                             {x | x IN s /\ f x IN u} <=>
                     open_in (subtopology euclidean t) u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  MATCH_MP_TAC CLOSED_MAP_IMP_QUOTIENT_MAP THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_IMP_CLOSED_MAP THEN
  ASM_REWRITE_TAC[]);;

let CONTINUOUS_ON_INVERSE = prove
 (`!f:real^M->real^N g s.
        f continuous_on s /\ compact s /\ (!x. x IN s ==> (g(f(x)) = x))
        ==> g continuous_on (IMAGE f s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_CLOSED] THEN
  SUBGOAL_THEN `IMAGE g (IMAGE (f:real^M->real^N) s) = s` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[CLOSED_IN_CLOSED] THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) t` THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    ASM_MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED; CLOSED_IN_CLOSED_TRANS;
                  BOUNDED_SUBSET; CONTINUOUS_ON_SUBSET];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
    ASM_MESON_TAC[CLOSED_IN_SUBSET; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBSET]]);;

let HOMEOMORPHISM_COMPACT = prove
 (`!s f t. compact s /\ f continuous_on s /\ (IMAGE f s = t) /\
           (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> ?g. homeomorphism(s,t) (f,g)`,
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE] THEN REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC[EXTENSION; homeomorphism] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  ASM_MESON_TAC[CONTINUOUS_ON_INVERSE; IN_IMAGE]);;

let HOMEOMORPHIC_COMPACT = prove
 (`!s f t. compact s /\ f continuous_on s /\ (IMAGE f s = t) /\
           (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> s homeomorphic t`,
  REWRITE_TAC[homeomorphic] THEN MESON_TAC[HOMEOMORPHISM_COMPACT]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas about composition of homeomorphisms.                               *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHISM_FROM_COMPOSITION_SURJECTIVE = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s = t /\
        g continuous_on t /\ IMAGE g t SUBSET u /\
        (?h. homeomorphism (s,u) (g o f,h))
        ==> (?f'. homeomorphism (s,t) (f,f')) /\
            (?g'. homeomorphism (t,u) (g,g'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism; o_THM]) THEN
  MATCH_MP_TAC(TAUT `q /\ (q ==> p) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_INJECTIVE_OPEN_MAP THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC OPEN_MAP_FROM_COMPOSITION_SURJECTIVE THEN
    MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `s:real^M->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`h:real^P->real^M`; `s:real^M->bool`] THEN
    ASM_REWRITE_TAC[homeomorphism; o_THM];
    REWRITE_TAC[homeomorphism; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':real^P->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(h:real^P->real^M) o (g:real^N->real^P)` THEN
    ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]]);;

let HOMEOMORPHISM_FROM_COMPOSITION_INJECTIVE = prove
 (`!f:real^M->real^N g:real^N->real^P s t u.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET u /\
        (!x y. x IN t /\ y IN t /\ g x = g y ==> x = y) /\
        (?h. homeomorphism (s,u) (g o f,h))
        ==> (?f'. homeomorphism (s,t) (f,f')) /\
            (?g'. homeomorphism (t,u) (g,g'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism; o_THM]) THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_INJECTIVE_OPEN_MAP THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC OPEN_MAP_FROM_COMPOSITION_INJECTIVE THEN
    MAP_EVERY EXISTS_TAC [`g:real^N->real^P`; `u:real^P->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`h:real^P->real^M`; `s:real^M->bool`] THEN
    ASM_REWRITE_TAC[homeomorphism; o_THM];
    REWRITE_TAC[homeomorphism; o_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real^N->real^M` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(f:real^M->real^N) o (h:real^P->real^M)` THEN
    ASM_SIMP_TAC[o_THM; IMAGE_o] THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Preservation of topological properties.                                   *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_COMPACTNESS = prove
 (`!s t. s homeomorphic t ==> (compact s <=> compact t)`,
  REWRITE_TAC[homeomorphic; homeomorphism] THEN
  MESON_TAC[COMPACT_CONTINUOUS_IMAGE]);;

let HOMEOMORPHIC_CONNECTEDNESS = prove
 (`!s t. s homeomorphic t ==> (connected s <=> connected t)`,
  REWRITE_TAC[homeomorphic; homeomorphism] THEN
  MESON_TAC[CONNECTED_CONTINUOUS_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Results on translation, scaling etc.                                      *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_SCALING = prove
 (`!s:real^N->bool c. ~(c = &0) ==> s homeomorphic (IMAGE (\x. c % x) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^N. c % x`; `\x:real^N. inv(c) % x`] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RINV] THEN
  SIMP_TAC[VECTOR_MUL_LID; IN_IMAGE; REAL_MUL_LID] THEN MESON_TAC[]);;

let HOMEOMORPHIC_TRANSLATION = prove
 (`!s a:real^N. s homeomorphic (IMAGE (\x. a + x) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^N. a +  x`; `\x:real^N. --a + x`] THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
  SIMP_TAC[VECTOR_ADD_ASSOC; VECTOR_ADD_LINV; VECTOR_ADD_RINV;
           FORALL_IN_IMAGE; VECTOR_ADD_LID] THEN
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

let HOMEOMORPHIC_AFFINITY = prove
 (`!s a:real^N c. ~(c = &0) ==> s homeomorphic (IMAGE (\x. a + c % x) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN
  EXISTS_TAC `IMAGE (\x:real^N. c % x) s` THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_SCALING] THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o; HOMEOMORPHIC_TRANSLATION]);;

let [HOMEOMORPHIC_BALLS; HOMEOMORPHIC_CBALLS; HOMEOMORPHIC_SPHERES] =
  (CONJUNCTS o prove)
 (`(!a:real^N b:real^N d e.
      &0 < d /\ &0 < e ==> ball(a,d) homeomorphic ball(b,e)) /\
   (!a:real^N b:real^N d e.
      &0 < d /\ &0 < e ==> cball(a,d) homeomorphic cball(b,e)) /\
   (!a:real^N b:real^N d e.
      &0 < d /\ &0 < e ==> sphere(a,d) homeomorphic sphere(b,e))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  EXISTS_TAC `\x:real^N. b + (e / d) % (x - a)` THEN
  EXISTS_TAC `\x:real^N. a + (d / e) % (x - b)` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CMUL;
    CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID; IN_BALL; IN_CBALL; IN_SPHERE] THEN
  REWRITE_TAC[dist; VECTOR_ARITH `a - (a + b) = --b:real^N`; NORM_NEG] THEN
  REWRITE_TAC[real_div; VECTOR_ARITH
   `a + d % ((b + e % (x - a)) - b) = (&1 - d * e) % a + (d * e) % x`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
    `(e * d') * (d * e') = (d * d') * (e * e')`] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID; REAL_SUB_REFL] THEN
  REWRITE_TAC[NORM_MUL; VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ARITH
   `&0 < x ==> (abs x = x)`] THEN
  GEN_REWRITE_TAC(BINOP_CONV o BINDER_CONV o funpow 2 RAND_CONV)
        [GSYM REAL_MUL_RID] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b) * c = (a * c) * b`] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ; GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID;
    GSYM REAL_MUL_ASSOC; REAL_LT_LMUL_EQ; REAL_LT_LDIV_EQ; NORM_SUB] THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; REAL_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* Homeomorphism of one-point compactifications.                             *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_ONE_POINT_COMPACTIFICATIONS = prove
 (`!s:real^M->bool t:real^N->bool a b.
        compact s /\ compact t /\ a IN s /\ b IN t /\
        (s DELETE a) homeomorphic (t DELETE b)
        ==> s homeomorphic t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic]) THEN
  REWRITE_TAC[HOMEOMORPHISM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `\x. if x = a then b else (f:real^M->real^N) x` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:real^M = a` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[continuous_within] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`b:real^N`; `e:real`] CENTRE_IN_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
      `closed_in (subtopology euclidean s)
                 { x | x IN (s DELETE a) /\
                       (f:real^M->real^N)(x) IN t DIFF ball(b,e)}`
    MP_TAC THENL
     [MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN SUBGOAL_THEN
       `{x | x IN s DELETE a /\ f x IN t DIFF ball(b,e)} =
        IMAGE (g:real^N->real^M) (t DIFF ball (b,e))`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_SIMP_TAC[COMPACT_DIFF; OPEN_BALL] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[];
      REWRITE_TAC[closed_in; open_in; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      DISCH_THEN(MP_TAC o SPEC `a:real^M` o last o CONJUNCTS) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_DELETE] THEN
      SIMP_TAC[IMP_CONJ; DE_MORGAN_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[DIST_REFL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_BALL]) THEN ASM SET_TAC[]];
    UNDISCH_TAC `(f:real^M->real^N) continuous_on (s DELETE a)` THEN
    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    REWRITE_TAC[continuous_within] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d (dist(a:real^M,x))` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; GSYM DIST_NZ] THEN
    ASM_MESON_TAC[REAL_LT_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Homeomorphisms between open intervals in real^1 and then in real^N.       *)
(* Could prove similar things for closed intervals, but they drop out of     *)
(* later stuff in "convex.ml" even more easily.                              *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_OPEN_INTERVALS_1 = prove
 (`!a b c d.
        drop a < drop b /\ drop c < drop d
        ==> interval(a,b) homeomorphic interval(c,d)`,
  SUBGOAL_THEN
   `!a b. drop a < drop b
          ==> interval(vec 0:real^1,vec 1) homeomorphic interval(a,b)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
    EXISTS_TAC `(\x. a + drop x % (b - a)):real^1->real^1` THEN
    EXISTS_TAC `(\x. inv(drop b - drop a) % (x - a)):real^1->real^1` THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ] THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_NEG; DROP_VEC; DROP_SUB] THEN
    REWRITE_TAC[REAL_ARITH `inv b * a:real = a / b`] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_SUB_LT;
       REAL_LT_ADDR; REAL_EQ_LDIV_EQ; REAL_DIV_RMUL; REAL_LT_IMP_NZ;
       REAL_LT_MUL; REAL_MUL_LZERO; REAL_ADD_SUB; REAL_LT_RMUL_EQ;
       REAL_ARITH `a + x < b <=> x < &1 * (b - a)`] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
      REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID];
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID]];
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`a:real^1`; `b:real^1`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^1`; `d:real^1`]) THEN
    ASM_REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [HOMEOMORPHIC_SYM] THEN
    REWRITE_TAC[HOMEOMORPHIC_TRANS]]);;

let HOMEOMORPHIC_OPEN_INTERVAL_UNIV_1 = prove
 (`!a b. drop a < drop b ==> interval(a,b) homeomorphic (:real^1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real^1`; `b:real^1`; `--vec 1:real^1`; `vec 1:real^1`]
        HOMEOMORPHIC_OPEN_INTERVALS_1) THEN
  ASM_REWRITE_TAC[DROP_VEC; DROP_NEG] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] HOMEOMORPHIC_TRANS) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[HOMEOMORPHIC_MINIMAL; IN_UNIV] THEN
  EXISTS_TAC `\x:real^1. inv(&1 - norm x) % x` THEN
  EXISTS_TAC `\y. if &0 <= drop y then inv(&1 + drop y) % y
                  else inv(&1 - drop y) % y` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
    REWRITE_TAC[DROP_NEG; DROP_VEC; DROP_CMUL; NORM_REAL; GSYM drop] THEN
    SIMP_TAC[REAL_LE_MUL_EQ; REAL_LT_INV_EQ; REAL_LE_MUL_EQ; REAL_ARITH
     `--a < x /\ x < a ==> &0 < a - abs x`] THEN
    SIMP_TAC[real_abs; VECTOR_MUL_ASSOC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    X_GEN_TAC `y:real^1` THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC; REAL_BOUNDS_LT] THEN
    REWRITE_TAC[DROP_CMUL; REAL_ABS_MUL; REAL_ABS_INV] THEN
    REWRITE_TAC[GSYM(ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div)] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 <= x ==> &0 < abs(&1 + x)`;
                 REAL_ARITH `~(&0 <= x) ==> &0 < abs(&1 - x)`] THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[NORM_REAL; VECTOR_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM drop; DROP_CMUL; REAL_ABS_MUL] THEN
    ASM_REWRITE_TAC[real_abs; REAL_LE_INV_EQ] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> &0 <= &1 + x`;
                 REAL_ARITH `~(&0 <= x) ==> &0 <= &1 - x`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM VECTOR_MUL_LID] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
    X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; DROP_VEC] THEN
    DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
    REWRITE_TAC[CONTINUOUS_AT_ID] THEN
    ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_INV THEN
    REWRITE_TAC[NETLIMIT_AT; o_DEF; LIFT_SUB; LIFT_DROP] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_SUB THEN
      SIMP_TAC[CONTINUOUS_CONST; REWRITE_RULE[o_DEF] CONTINUOUS_AT_LIFT_NORM];
      REWRITE_TAC[NORM_REAL; GSYM drop] THEN ASM_REAL_ARITH_TAC];
    SUBGOAL_THEN `(:real^1) = {x | x$1 >= &0} UNION {x | x$1 <= &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_UNION; IN_ELIM_THM; IN_UNIV] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE; CLOSED_HALFSPACE_COMPONENT_GE;
                  IN_ELIM_THM] THEN
      REWRITE_TAC[GSYM drop; REAL_NOT_LE; real_ge; REAL_LET_ANTISYM] THEN
      SIMP_TAC[REAL_LE_ANTISYM; REAL_SUB_RZERO; REAL_ADD_RID] THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_ELIM_THM; real_ge] THEN
      DISCH_TAC THEN MATCH_MP_TAC CONTINUOUS_MUL THEN
      REWRITE_TAC[CONTINUOUS_AT_ID] THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN MATCH_MP_TAC CONTINUOUS_INV THEN
      REWRITE_TAC[NETLIMIT_AT; o_DEF; LIFT_ADD; LIFT_SUB; LIFT_DROP] THEN
      ASM_SIMP_TAC[CONTINUOUS_ADD; CONTINUOUS_AT_ID; CONTINUOUS_SUB;
                   CONTINUOUS_CONST] THEN
      ASM_REAL_ARITH_TAC]]);;

let HOMEOMORPHIC_OPEN_INTERVALS = prove
 (`!a b:real^N c d:real^N.
        (interval(a,b) = {} <=> interval(c,d) = {})
        ==> interval(a,b) homeomorphic interval(c,d)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `interval(c:real^N,d) = {}` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[HOMEOMORPHIC_REFL] THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> interval(lift((a:real^N)$i),lift((b:real^N)$i)) homeomorphic
            interval(lift((c:real^N)$i),lift((d:real^N)$i))`
  MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_OPEN_INTERVALS_1; LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[HOMEOMORPHIC_MINIMAL; IN_INTERVAL_1; LIFT_DROP] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:num->real^1->real^1`; `g:num->real^1->real^1`] THEN
  DISCH_TAC THEN
  EXISTS_TAC
   `(\x. lambda i.
       drop((f:num->real^1->real^1) i (lift(x$i)))):real^N->real^N` THEN
  EXISTS_TAC
   `(\x. lambda i.
       drop((g:num->real^1->real^1) i (lift(x$i)))):real^N->real^N` THEN
  ASM_SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; CART_EQ; LIFT_DROP] THEN
  ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  SIMP_TAC[LAMBDA_BETA; LIFT_DROP] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THENL
   [EXISTS_TAC `interval(lift((a:real^N)$i),lift((b:real^N)$i))`;
    EXISTS_TAC `interval(lift((c:real^N)$i),lift((d:real^N)$i))`] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1] THEN
  ASM_SIMP_TAC[LIFT_DROP; IN_INTERVAL]);;

let HOMEOMORPHIC_OPEN_INTERVAL_UNIV = prove
 (`!a b:real^N.
        ~(interval(a,b) = {})
        ==> interval(a,b) homeomorphic (:real^N)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. 1 <= i /\ i <= dimindex(:N)
        ==> interval(lift((a:real^N)$i),lift((b:real^N)$i)) homeomorphic
            (:real^1)`
  MP_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_OPEN_INTERVAL_UNIV_1; LIFT_DROP];
    ALL_TAC] THEN
  REWRITE_TAC[HOMEOMORPHIC_MINIMAL; IN_INTERVAL_1; LIFT_DROP] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`f:num->real^1->real^1`; `g:num->real^1->real^1`] THEN
  DISCH_TAC THEN
  EXISTS_TAC
   `(\x. lambda i.
       drop((f:num->real^1->real^1) i (lift(x$i)))):real^N->real^N` THEN
  EXISTS_TAC
   `(\x. lambda i.
       drop((g:num->real^1->real^1) i (lift(x$i)))):real^N->real^N` THEN
  ASM_SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; CART_EQ; LIFT_DROP; IN_UNIV] THEN
  ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  SIMP_TAC[LAMBDA_BETA; LIFT_DROP] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THENL
   [EXISTS_TAC `interval(lift((a:real^N)$i),lift((b:real^N)$i))`;
    EXISTS_TAC `(:real^1)`] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; IN_UNIV] THEN
  ASM_SIMP_TAC[LIFT_DROP; IN_INTERVAL]);;

let HOMEOMORPHIC_BALL_UNIV = prove
 (`!a:real^N r. &0 < r ==> ball(a,r) homeomorphic (:real^N)`,
  REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `a:real^N` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?y:real^N. r = norm(y)` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[VECTOR_CHOOSE_SIZE; REAL_LT_IMP_LE]; POP_ASSUM MP_TAC] THEN
  REWRITE_TAC[NORM_POS_LT] THEN GEOM_NORMALIZE_TAC `y:real^N` THEN
  SIMP_TAC[] THEN GEN_TAC THEN REPEAT(DISCH_THEN(K ALL_TAC)) THEN
  REWRITE_TAC[HOMEOMORPHIC_MINIMAL] THEN
  EXISTS_TAC `\z:real^N. inv(&1 - norm(z)) % z` THEN
  EXISTS_TAC `\z:real^N. inv(&1 + norm(z)) % z` THEN
  REWRITE_TAC[IN_BALL; IN_UNIV; DIST_0; VECTOR_MUL_ASSOC; VECTOR_MUL_EQ_0;
              VECTOR_ARITH `a % x:real^N = x <=> (a - &1) % x = vec 0`] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN DISJ1_TAC THEN
    REWRITE_TAC[GSYM REAL_INV_MUL; REAL_SUB_0; REAL_INV_EQ_1] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `x < &1 ==> abs(&1 - x) = &1 - x`] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD;
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_ARITH
     `&0 <= y ==> inv(abs(&1 + y)) * z = z / (&1 + y)`] THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_LDIV_EQ; REAL_ARITH
      `&0 <= y ==> &0 < &1 + y`] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; DISJ1_TAC] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL; REAL_SUB_0; REAL_INV_EQ_1] THEN
    MP_TAC(ISPEC `y:real^N` NORM_POS_LE) THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN
    SIMP_TAC[IN_BALL_0; REAL_SUB_0; REAL_ARITH `x < &1 ==> ~(&1 = x)`] THEN
    REWRITE_TAC[o_DEF; LIFT_SUB] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_ON_ID];
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN
    SIMP_TAC[NORM_POS_LE; REAL_ARITH `&0 <= x ==> ~(&1 + x = &0)`] THEN
    REWRITE_TAC[o_DEF; LIFT_ADD] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    REWRITE_TAC[CONTINUOUS_ON_ID]]);;

(* ------------------------------------------------------------------------- *)
(* Cardinalities of various useful sets.                                     *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_EUCLIDEAN = prove
 (`(:real^N) =_c (:real)`,
  MATCH_MP_TAC CARD_EQ_CART THEN REWRITE_TAC[real_INFINITE]);;

let UNCOUNTABLE_EUCLIDEAN = prove
 (`~COUNTABLE(:real^N)`,
  MATCH_MP_TAC CARD_EQ_REAL_IMP_UNCOUNTABLE THEN
  REWRITE_TAC[CARD_EQ_EUCLIDEAN]);;

let CARD_EQ_INTERVAL = prove
 (`(!a b:real^N. ~(interval(a,b) = {}) ==> interval[a,b] =_c (:real)) /\
   (!a b:real^N. ~(interval(a,b) = {}) ==> interval(a,b) =_c (:real))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `interval(a:real^N,b) = {}` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
    REWRITE_TAC[CARD_LE_UNIV] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    REWRITE_TAC[CARD_EQ_EUCLIDEAN];
    TRANS_TAC CARD_LE_TRANS `interval(a:real^N,b)` THEN
    SIMP_TAC[CARD_LE_SUBSET; INTERVAL_OPEN_SUBSET_CLOSED];
    TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
    REWRITE_TAC[CARD_LE_UNIV] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    REWRITE_TAC[CARD_EQ_EUCLIDEAN];
    ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
  SIMP_TAC[ONCE_REWRITE_RULE[CARD_EQ_SYM] CARD_EQ_IMP_LE;
           CARD_EQ_EUCLIDEAN] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_OPEN_INTERVAL_UNIV) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CARD_EQ) THEN
  MESON_TAC[CARD_EQ_IMP_LE; CARD_EQ_SYM]);;

let UNCOUNTABLE_INTERVAL = prove
 (`(!a b. ~(interval(a,b) = {}) ==> ~COUNTABLE(interval[a,b])) /\
   (!a b. ~(interval(a,b) = {}) ==> ~COUNTABLE(interval(a,b)))`,
  SIMP_TAC[CARD_EQ_REAL_IMP_UNCOUNTABLE; CARD_EQ_INTERVAL]);;

let COUNTABLE_OPEN_INTERVAL = prove
 (`!a b. COUNTABLE(interval(a,b)) <=> interval(a,b) = {}`,
  MESON_TAC[COUNTABLE_EMPTY; UNCOUNTABLE_INTERVAL]);;

let CARD_EQ_OPEN = prove
 (`!s:real^N->bool. open s /\ ~(s = {}) ==> s =_c (:real)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
    REWRITE_TAC[CARD_LE_UNIV] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    REWRITE_TAC[CARD_EQ_EUCLIDEAN];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_INTERVAL]) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `c:real^N`) THEN
    DISCH_THEN(MP_TAC o SPEC `c:real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
    ASM_CASES_TAC `interval(a:real^N,b) = {}` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN STRIP_TAC THEN
    TRANS_TAC CARD_LE_TRANS `interval[a:real^N,b]` THEN
    ASM_SIMP_TAC[CARD_LE_SUBSET] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN ASM_SIMP_TAC[CARD_EQ_INTERVAL]]);;

let UNCOUNTABLE_OPEN = prove
 (`!s:real^N->bool. open s /\ ~(s = {}) ==> ~(COUNTABLE s)`,
  SIMP_TAC[CARD_EQ_OPEN; CARD_EQ_REAL_IMP_UNCOUNTABLE]);;

let CARD_EQ_BALL = prove
 (`!a:real^N r. &0 < r ==> ball(a,r) =_c (:real)`,
  SIMP_TAC[CARD_EQ_OPEN; OPEN_BALL; BALL_EQ_EMPTY; GSYM REAL_NOT_LT]);;

let CARD_EQ_CBALL = prove
 (`!a:real^N r. &0 < r ==> cball(a,r) =_c (:real)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
    REWRITE_TAC[CARD_LE_UNIV] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    REWRITE_TAC[CARD_EQ_EUCLIDEAN];
    TRANS_TAC CARD_LE_TRANS `ball(a:real^N,r)` THEN
    SIMP_TAC[CARD_LE_SUBSET; BALL_SUBSET_CBALL] THEN
    MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN ASM_SIMP_TAC[CARD_EQ_BALL]]);;

let FINITE_IMP_NOT_OPEN = prove
 (`!s:real^N->bool. FINITE s /\ ~(s = {}) ==> ~(open s)`,
  MESON_TAC[UNCOUNTABLE_OPEN; FINITE_IMP_COUNTABLE]);;

let OPEN_IMP_INFINITE = prove
 (`!s. open s ==> s = {} \/ INFINITE s`,
  MESON_TAC[FINITE_IMP_NOT_OPEN; INFINITE]);;

let EMPTY_INTERIOR_FINITE = prove
 (`!s:real^N->bool. FINITE s ==> interior s = {}`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `s:real^N->bool` OPEN_INTERIOR) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] FINITE_IMP_NOT_OPEN) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[INTERIOR_SUBSET]);;

let CARD_EQ_CONNECTED = prove
 (`!s a b:real^N.
        connected s /\ a IN s /\ b IN s /\ ~(a = b) ==> s =_c (:real)`,
  GEOM_ORIGIN_TAC `b:real^N` THEN GEOM_NORMALIZE_TAC `a:real^N` THEN
  REWRITE_TAC[NORM_EQ_SQUARE; REAL_POS; REAL_POW_ONE] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
    SIMP_TAC[CARD_LE_UNIV; CARD_EQ_EUCLIDEAN; CARD_EQ_IMP_LE];
    TRANS_TAC CARD_LE_TRANS `interval[vec 0:real^1,vec 1]` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ONCE_REWRITE_RULE[CARD_EQ_SYM] CARD_EQ_IMP_LE) THEN
      SIMP_TAC[UNIT_INTERVAL_NONEMPTY; CARD_EQ_INTERVAL];
      REWRITE_TAC[LE_C] THEN EXISTS_TAC `\x:real^N. lift(a dot x)` THEN
      SIMP_TAC[FORALL_LIFT; LIFT_EQ; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC CONNECTED_IVT_HYPERPLANE THEN
      MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `a:real^N`] THEN
      ASM_REWRITE_TAC[DOT_RZERO]]]);;

let UNCOUNTABLE_CONNECTED = prove
 (`!s a b:real^N.
        connected s /\ a IN s /\ b IN s /\ ~(a = b) ==> ~COUNTABLE s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CARD_EQ_REAL_IMP_UNCOUNTABLE THEN
  MATCH_MP_TAC CARD_EQ_CONNECTED THEN
  ASM_MESON_TAC[]);;

let CARD_LT_IMP_DISCONNECTED = prove
 (`!s x:real^N. s <_c (:real) /\ x IN s ==> connected_component s x = {x}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SET_RULE
   `s = {a} <=> a IN s /\ !a b. a IN s /\ b IN s /\ ~(a = b) ==> F`] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN] THEN
  ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN
  MP_TAC(ISPECL [`connected_component s (x:real^N)`; `a:real^N`; `b:real^N`]
        CARD_EQ_CONNECTED) THEN
  ASM_REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT] THEN
  DISCH_TAC THEN UNDISCH_TAC `(s:real^N->bool) <_c (:real)` THEN
  REWRITE_TAC[CARD_NOT_LT] THEN
  TRANS_TAC CARD_LE_TRANS `connected_component s (x:real^N)` THEN
  ASM_SIMP_TAC[ONCE_REWRITE_RULE[CARD_EQ_SYM] CARD_EQ_IMP_LE] THEN
  MATCH_MP_TAC CARD_LE_SUBSET THEN REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]);;

let COUNTABLE_IMP_DISCONNECTED = prove
 (`!s x:real^N. COUNTABLE s /\ x IN s ==> connected_component s x = {x}`,
  SIMP_TAC[CARD_LT_IMP_DISCONNECTED; COUNTABLE_IMP_CARD_LT_REAL]);;

let CONNECTED_CARD_EQ_IFF_NONTRIVIAL = prove
 (`!s:real^N->bool.
        connected s ==> (s =_c (:real) <=> ~(?a. s SUBSET {a}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ALL_TAC; MATCH_MP_TAC CARD_EQ_CONNECTED THEN ASM SET_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
  REWRITE_TAC[FINITE_SING] THEN
  ASM_MESON_TAC[CARD_EQ_REAL_IMP_UNCOUNTABLE; FINITE_IMP_COUNTABLE]);;

(* ------------------------------------------------------------------------- *)
(* "Iff" forms of constancy of function from connected set into a set that   *)
(* is smaller than R, or countable, or finite, or disconnected, or discrete. *)
(* ------------------------------------------------------------------------- *)

let [CONTINUOUS_DISCONNECTED_RANGE_CONSTANT_EQ;
     CONTINUOUS_DISCRETE_RANGE_CONSTANT_EQ;
     CONTINUOUS_FINITE_RANGE_CONSTANT_EQ] = (CONJUNCTS o prove)
  (`(!s. connected s <=>
         !f:real^M->real^N t.
            f continuous_on s /\ IMAGE f s SUBSET t /\
            (!y. y IN t ==> connected_component t y = {y})
            ==> ?a. !x. x IN s ==> f x = a) /\
    (!s. connected s <=>
         !f:real^M->real^N.
            f continuous_on s /\
            (!x. x IN s
                 ==> ?e. &0 < e /\
                         !y. y IN s /\ ~(f y = f x) ==> e <= norm(f y - f x))
            ==> ?a. !x. x IN s ==> f x = a) /\
    (!s. connected s <=>
         !f:real^M->real^N.
            f continuous_on s /\ FINITE(IMAGE f s)
            ==> ?a. !x. x IN s ==> f x = a)`,
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `s:real^M->bool` THEN
  MATCH_MP_TAC(TAUT
   `(s ==> t) /\ (t ==> u) /\ (u ==> v) /\ (v ==> s)
    ==> (s <=> t) /\ (s <=> u) /\ (s <=> v)`) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^M->bool = {}` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^M` o
        GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    EXISTS_TAC `(f:real^M->real^N) x` THEN
    MATCH_MP_TAC(SET_RULE
     `IMAGE f s SUBSET {a} ==> !y. y IN s ==> f y = a`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^M->real^N) x`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    ASM_SIMP_TAC[CONNECTED_CONTINUOUS_IMAGE] THEN ASM SET_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `IMAGE (f:real^M->real^N) s` THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; SUBSET_REFL] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(SET_RULE
     `(!y. y IN s /\ f y IN connected_component (IMAGE f s) a ==> f y = a) /\
      connected_component (IMAGE f s) a SUBSET (IMAGE f s) /\
      connected_component (IMAGE f s) a a
      ==> connected_component (IMAGE f s) a = {a}`) THEN
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET; CONNECTED_COMPONENT_REFL_EQ] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
    MP_TAC(ISPEC `connected_component (IMAGE (f:real^M->real^N) s) (f x)`
        CONNECTED_CLOSED) THEN
    REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC
     [`cball((f:real^M->real^N) x,e / &2)`;
      `(:real^N) DIFF ball((f:real^M->real^N) x,e)`] THEN
    REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_BALL; CLOSED_CBALL] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL; IN_UNION; IN_DIFF; IN_BALL; IN_UNIV] THEN
      MATCH_MP_TAC(MESON[SUBSET; CONNECTED_COMPONENT_SUBSET]
       `(!x. x IN s ==> P x)
        ==> (!x. x IN connected_component s y ==> P x)`) THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^M` THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z:real^M`) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NORM_ARITH;
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s /\ x IN t ==> F) ==> s INTER t INTER u = {}`) THEN
      REWRITE_TAC[IN_BALL; IN_CBALL; IN_DIFF; IN_UNIV] THEN
      UNDISCH_TAC `&0 < e` THEN CONV_TAC NORM_ARITH;
      EXISTS_TAC `(f:real^M->real^N) x` THEN
      ASM_SIMP_TAC[CENTRE_IN_CBALL; REAL_HALF; REAL_LT_IMP_LE; IN_INTER] THEN
      REWRITE_TAC[IN] THEN
      ASM_SIMP_TAC[CONNECTED_COMPONENT_REFL_EQ; FUN_IN_IMAGE];
      EXISTS_TAC `(f:real^M->real^N) y` THEN
      ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV; IN_BALL; REAL_NOT_LT] THEN
      ASM_SIMP_TAC[ONCE_REWRITE_RULE[DIST_SYM] dist]];
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `f:real^M->real^N` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MATCH_MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    ASM_CASES_TAC `IMAGE (f:real^M->real^N) s DELETE (f x) = {}` THENL
     [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC
     `inf{norm(z - f x) |z| z IN IMAGE (f:real^M->real^N) s DELETE (f x)}` THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[REAL_LT_INF_FINITE; REAL_INF_LE_FINITE; FINITE_DELETE;
                 FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[IN_DELETE; NORM_POS_LT; VECTOR_SUB_EQ; IN_IMAGE] THEN
    MESON_TAC[REAL_LE_REFL];
    REWRITE_TAC[CONNECTED_CLOSED_IN_EQ] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:real^M->bool`; `u:real^M->bool`] THEN
    STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC
     `(\x. if x IN t then vec 0 else basis 1):real^M->real^N`) THEN
    REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES_LOCAL THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_CONST] THEN ASM SET_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{vec 0:real^N,basis 1}` THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN SET_TAC[];
      SUBGOAL_THEN `?a b:real^M. a IN s /\ a IN t /\ b IN s /\ ~(b IN t)`
      STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; DISCH_THEN(CHOOSE_THEN MP_TAC)] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `a:real^M` th) THEN
                           MP_TAC(SPEC `b:real^M` th)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      CONV_TAC(RAND_CONV SYM_CONV) THEN
      SIMP_TAC[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1; REAL_LE_REFL]]]);;

let CONTINUOUS_DISCONNECTED_RANGE_CONSTANT = prove
 (`!f:real^M->real^N s.
        connected s /\
        f continuous_on s /\ IMAGE f s SUBSET t /\
        (!y. y IN t ==> connected_component t y = {y})
        ==> ?a. !x. x IN s ==> f x = a`,
  MESON_TAC[CONTINUOUS_DISCONNECTED_RANGE_CONSTANT_EQ]);;

let CONTINUOUS_DISCRETE_RANGE_CONSTANT = prove
 (`!f:real^M->real^N s.
        connected s /\
        f continuous_on s /\
        (!x. x IN s
             ==> ?e. &0 < e /\
                     !y. y IN s /\ ~(f y = f x) ==> e <= norm(f y - f x))
        ==> ?a. !x. x IN s ==> f x = a`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONTINUOUS_DISCRETE_RANGE_CONSTANT_EQ]);;

let CONTINUOUS_FINITE_RANGE_CONSTANT = prove
 (`!f:real^M->real^N s.
        connected s /\
        f continuous_on s /\
        FINITE(IMAGE f s)
        ==> ?a. !x. x IN s ==> f x = a`,
  MESON_TAC[CONTINUOUS_FINITE_RANGE_CONSTANT_EQ]);;

let CONTINUOUS_COUNTABLE_RANGE_CONSTANT_EQ = prove
 (`!s. connected s <=>
         !f:real^M->real^N.
            f continuous_on s /\ COUNTABLE(IMAGE f s)
            ==> ?a. !x. x IN s ==> f x = a`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_DISCONNECTED_RANGE_CONSTANT_EQ];
    REWRITE_TAC[CONTINUOUS_FINITE_RANGE_CONSTANT_EQ]] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FINITE_IMP_COUNTABLE] THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) s` THEN
  ASM_SIMP_TAC[COUNTABLE_IMP_DISCONNECTED; SUBSET_REFL]);;

let CONTINUOUS_CARD_LT_RANGE_CONSTANT_EQ = prove
 (`!s. connected s <=>
         !f:real^M->real^N.
            f continuous_on s /\ (IMAGE f s) <_c (:real)
            ==> ?a. !x. x IN s ==> f x = a`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_DISCONNECTED_RANGE_CONSTANT_EQ];
    REWRITE_TAC[CONTINUOUS_COUNTABLE_RANGE_CONSTANT_EQ]] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[COUNTABLE_IMP_CARD_LT_REAL] THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) s` THEN
  ASM_SIMP_TAC[CARD_LT_IMP_DISCONNECTED; SUBSET_REFL]);;

let CONTINUOUS_COUNTABLE_RANGE_CONSTANT = prove
 (`!f:real^M->real^N s.
        connected s /\ f continuous_on s /\ COUNTABLE(IMAGE f s)
        ==> ?a. !x. x IN s ==> f x = a`,
  MESON_TAC[CONTINUOUS_COUNTABLE_RANGE_CONSTANT_EQ]);;

let CONTINUOUS_CARD_LT_RANGE_CONSTANT = prove
 (`!f:real^M->real^N s.
        connected s /\ f continuous_on s /\ (IMAGE f s) <_c (:real)
        ==> ?a. !x. x IN s ==> f x = a`,
  MESON_TAC[CONTINUOUS_CARD_LT_RANGE_CONSTANT_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Homeomorphism of hyperplanes.                                             *)
(* ------------------------------------------------------------------------- *)

let HOMEOMORPHIC_HYPERPLANES = prove
 (`!a:real^N b c:real^N d.
        ~(a = vec 0) /\ ~(c = vec 0)
        ==> {x | a dot x = b} homeomorphic {x | c dot x = d}`,
  let lemma = prove
   (`~(a = vec 0)
     ==> {x:real^N | a dot x = b} homeomorphic {x:real^N | x$1 = &0}`,
    REPEAT STRIP_TAC THEN SUBGOAL_THEN `?c:real^N. a dot c = b`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; VEC_COMPONENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `b / (a:real^N)$k % basis k:real^N` THEN
      ASM_SIMP_TAC[DOT_RMUL; DOT_BASIS; REAL_DIV_RMUL];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      ABBREV_TAC `p = {x:real^N | x$1 = &0}` THEN
      GEOM_ORIGIN_TAC `c:real^N` THEN
      REWRITE_TAC[VECTOR_ADD_RID; DOT_RADD; DOT_RZERO; REAL_EQ_ADD_LCANCEL_0;
                  REAL_ADD_RID] THEN
      REPEAT STRIP_TAC THEN UNDISCH_TAC `~(a:real^N = vec 0)` THEN
      GEOM_BASIS_MULTIPLE_TAC 1 `a:real^N` THEN
      SIMP_TAC[VECTOR_MUL_EQ_0; DE_MORGAN_THM; DOT_LMUL; REAL_ENTIRE] THEN
      SIMP_TAC[DOT_BASIS; LE_REFL; DIMINDEX_GE_1] THEN
      EXPAND_TAC "p" THEN REWRITE_TAC[HOMEOMORPHIC_REFL]]) in
  REPEAT STRIP_TAC THEN
  TRANS_TAC HOMEOMORPHIC_TRANS `{x:real^N | x$1 = &0}` THEN
  ASM_SIMP_TAC[lemma] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  ASM_SIMP_TAC[lemma]);;

let HOMEOMORPHIC_HYPERPLANE_STANDARD_HYPERPLANE = prove
 (`!a:real^N b k c.
        ~(a = vec 0) /\ 1 <= k /\ k <= dimindex(:N)
        ==> {x | a dot x = b} homeomorphic {x:real^N | x$k = c}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x:real^N | x$k = c} = {x | basis k dot x = c}` SUBST1_TAC
  THENL [ASM_SIMP_TAC[DOT_BASIS]; MATCH_MP_TAC HOMEOMORPHIC_HYPERPLANES] THEN
  ASM_SIMP_TAC[BASIS_NONZERO]);;

let HOMEOMORPHIC_STANDARD_HYPERPLANE_HYPERPLANE = prove
 (`!a:real^N b k c.
        ~(a = vec 0) /\ 1 <= k /\ k <= dimindex(:N)
        ==> {x:real^N | x$k = c} homeomorphic {x | a dot x = b}`,
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  REWRITE_TAC[HOMEOMORPHIC_HYPERPLANE_STANDARD_HYPERPLANE]);;

let HOMEOMORPHIC_HYPERPLANE_UNIV = prove
 (`!a b. ~(a = vec 0) /\ dimindex(:N) = dimindex(:M) + 1
         ==> {x:real^N | a dot x = b} homeomorphic (:real^M)`,
  REPEAT STRIP_TAC THEN TRANS_TAC HOMEOMORPHIC_TRANS
   `{x:real^N | basis(dimindex(:N)) dot x = &0}` THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_HYPERPLANES; BASIS_NONZERO;
               LE_REFL; DIMINDEX_GE_1] THEN
  REWRITE_TAC[homeomorphic; HOMEOMORPHISM] THEN
  EXISTS_TAC `(\x. lambda i. x$i):real^N->real^M` THEN
  EXISTS_TAC `(\x. lambda i. if i <= dimindex(:M) then x$i else &0)
              :real^M->real^N` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT];
    REWRITE_TAC[SUBSET_UNIV];
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    ASM_SIMP_TAC[DOT_BASIS; LAMBDA_BETA; LE_REFL; ARITH_RULE `1 <= n + 1`;
                 ARITH_RULE `~(m + 1 <= m)`];
    ASM_SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA; DOT_BASIS; LE_REFL; CART_EQ;
                 ARITH_RULE `1 <= n + 1`] THEN
    GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i = dimindex(:M) + 1` THEN ASM_REWRITE_TAC[COND_ID] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[LAMBDA_BETA; CART_EQ; IN_UNIV; LE_REFL;
                 ARITH_RULE `i <= n ==> i <= n + 1`]]);;

(* ------------------------------------------------------------------------- *)
(* "Isometry" (up to constant bounds) of injective linear map etc.           *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_ISOMETRIC = prove
 (`!f s e x.
        &0 < e /\ subspace s /\
        linear f /\ (!x. x IN s ==> norm(f x) >= e * norm(x)) /\
        (!n. x(n) IN s) /\ cauchy(f o x)
        ==> cauchy x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_ge] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[CAUCHY; dist; o_THM] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP LINEAR_SUB th)]) THEN
  DISCH_THEN(fun th -> X_GEN_TAC `d:real` THEN DISCH_TAC THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o SPEC `d * e`) THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  ASM_MESON_TAC[REAL_LE_RDIV_EQ; REAL_MUL_SYM; REAL_LET_TRANS; SUBSPACE_SUB;
                REAL_LT_LDIV_EQ]);;

let COMPLETE_ISOMETRIC_IMAGE = prove
 (`!f:real^M->real^N s e.
        &0 < e /\ subspace s /\
        linear f /\ (!x. x IN s ==> norm(f x) >= e * norm(x)) /\
        complete s
        ==> complete(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[complete; EXISTS_IN_IMAGE] THEN
  STRIP_TAC THEN X_GEN_TAC `g:num->real^N` THEN
  REWRITE_TAC[IN_IMAGE; SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->real^M` MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[GSYM o_DEF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num->real^M`) THEN
  ASM_MESON_TAC[CAUCHY_ISOMETRIC; LINEAR_CONTINUOUS_AT;
                CONTINUOUS_AT_SEQUENTIALLY]);;

let INJECTIVE_IMP_ISOMETRIC = prove
 (`!f:real^M->real^N s.
        closed s /\ subspace s /\
        linear f /\ (!x. x IN s /\ (f x = vec 0) ==> (x = vec 0))
        ==> ?e. &0 < e /\ !x. x IN s ==> norm(f x) >= e * norm(x)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s SUBSET {vec 0 :real^M}` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; REAL_MUL_LID; real_ge] THEN
    ASM_MESON_TAC[SUBSET; IN_SING; NORM_0; LINEAR_0; REAL_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [SUBSET]) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; IN_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^M` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`{(f:real^M->real^N) x | x IN s /\ norm(x) = norm(a:real^M)}`;
    `vec 0:real^N`] DISTANCE_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    SUBST1_TAC(SET_RULE
     `{f x | x IN s /\ norm(x) = norm(a:real^M)} =
      IMAGE (f:real^M->real^N) (s INTER {x | norm x = norm a})`) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
    MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{x:real^M | norm x = norm(a:real^M)} = frontier(cball(vec 0,norm a))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[FRONTIER_CBALL; NORM_POS_LT; dist; VECTOR_SUB_LZERO;
                   NORM_NEG; sphere];
      ASM_SIMP_TAC[COMPACT_FRONTIER; COMPACT_CBALL]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SET_RULE `{f x | P x} = IMAGE f {x | P x}`] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M` MP_TAC) THEN
  REWRITE_TAC[IN_ELIM_THM; dist; VECTOR_SUB_LZERO; NORM_NEG] THEN
  STRIP_TAC THEN REWRITE_TAC[CLOSED_LIMPT; LIMPT_APPROACHABLE] THEN
  EXISTS_TAC `norm((f:real^M->real^N) b) / norm(b)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LT_DIV; NORM_POS_LT; NORM_EQ_0]; ALL_TAC] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:real^M = vec 0` THENL
   [FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
    REWRITE_TAC[NORM_0; REAL_MUL_RZERO; real_ge; REAL_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(norm(a:real^M) / norm(x)) % x:real^M`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0] THEN ASM_MESON_TAC[subspace];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; real_ge] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; NORM_POS_LT] THEN
  REWRITE_TAC[real_div; REAL_MUL_AC]);;

let CLOSED_INJECTIVE_IMAGE_SUBSPACE = prove
 (`!f s. subspace s /\
         linear f /\
         (!x. x IN s /\ f(x) = vec 0 ==> x = vec 0) /\
         closed s
         ==> closed(IMAGE f s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM COMPLETE_EQ_CLOSED] THEN
  MATCH_MP_TAC COMPLETE_ISOMETRIC_IMAGE THEN
  ASM_REWRITE_TAC[COMPLETE_EQ_CLOSED] THEN
  MATCH_MP_TAC INJECTIVE_IMP_ISOMETRIC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Relating linear images to open/closed/interior/closure.                   *)
(* ------------------------------------------------------------------------- *)

let OPEN_SURJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> !s. open s ==> open(IMAGE f s)`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[open_def; FORALL_IN_IMAGE] THEN
  FIRST_ASSUM(MP_TAC o GEN `k:num` o SPEC `basis k:real^N`) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `bounded(IMAGE (b:num->real^M) (1..dimindex(:N)))` MP_TAC THENL
   [SIMP_TAC[FINITE_IMP_BOUNDED; FINITE_IMAGE; FINITE_NUMSEG]; ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `s:real^M->bool` THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `x:real^M` THEN ASM_CASES_TAC `(x:real^M) IN s` THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / B / &(dimindex(:N))` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; DIMINDEX_GE_1; LE_1] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
  ABBREV_TAC `u = y - (f:real^M->real^N) x` THEN
  EXISTS_TAC `x + vsum(1..dimindex(:N)) (\i. (u:real^N)$i % b i):real^M` THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_VSUM; FINITE_NUMSEG; o_DEF;
               LINEAR_CMUL; BASIS_EXPANSION] THEN
  CONJ_TAC THENL [EXPAND_TAC "u" THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[NORM_ARITH `dist(x + y,x) = norm y`] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(dist(y,(f:real^M->real^N) x) * &(dimindex(:N))) * B` THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; DIMINDEX_GE_1; LE_1] THEN
  MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * a * c`] THEN
  GEN_REWRITE_TAC(RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
  MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[NORM_MUL; dist] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM]);;

let OPEN_BIJECTIVE_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> (open(IMAGE f s) <=> open s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[OPEN_SURJECTIVE_LINEAR_IMAGE]] THEN
  SUBGOAL_THEN `s = {x | (f:real^M->real^N) x IN IMAGE f s}`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT]);;

add_linear_invariants [OPEN_BIJECTIVE_LINEAR_IMAGE_EQ];;

let CLOSED_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> !s. closed s ==> closed(IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) (:real^M)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`g:real^N->real^M`; `IMAGE (f:real^M->real^N) (:real^M)`;
                   `IMAGE (g:real^N->real^M) (IMAGE (f:real^M->real^N) s)`]
        CONTINUOUS_CLOSED_IN_PREIMAGE) THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM IMAGE_o; IMAGE_I]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    REWRITE_TAC[EXTENSION; o_THM; I_THM] THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_INJECTIVE_IMAGE_SUBSPACE THEN
    ASM_REWRITE_TAC[IN_UNIV; SUBSPACE_UNIV; CLOSED_UNIV] THEN
    X_GEN_TAC `x:real^M` THEN
    DISCH_THEN(MP_TAC o AP_TERM `g:real^N->real^M`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM; I_THM; o_THM]) THEN
    ASM_MESON_TAC[LINEAR_0]]);;

let CLOSED_INJECTIVE_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (closed(IMAGE f s) <=> closed s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC; ASM_MESON_TAC[CLOSED_INJECTIVE_LINEAR_IMAGE]] THEN
  SUBGOAL_THEN `s = {x | (f:real^M->real^N) x IN IMAGE f s}`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT]);;

add_linear_invariants [CLOSED_INJECTIVE_LINEAR_IMAGE_EQ];;

let CLOSURE_LINEAR_IMAGE_SUBSET = prove
 (`!f:real^M->real^N s.
        linear f ==> IMAGE f (closure s) SUBSET closure(IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
  ASM_SIMP_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET; LINEAR_CONTINUOUS_ON]);;

let CLOSURE_INJECTIVE_LINEAR_IMAGE  = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> closure(IMAGE f s) = IMAGE f (closure s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[CLOSURE_LINEAR_IMAGE_SUBSET] THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN
  SIMP_TAC[CLOSURE_SUBSET; IMAGE_SUBSET] THEN
  ASM_MESON_TAC[CLOSED_INJECTIVE_LINEAR_IMAGE; CLOSED_CLOSURE]);;

add_linear_invariants [CLOSURE_INJECTIVE_LINEAR_IMAGE];;

let CLOSURE_BOUNDED_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ bounded s
        ==> closure(IMAGE f s) = IMAGE f (closure s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[CLOSURE_LINEAR_IMAGE_SUBSET] THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN
  SIMP_TAC[CLOSURE_SUBSET; IMAGE_SUBSET] THEN
  MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
  MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN
  ASM_REWRITE_TAC[COMPACT_CLOSURE]);;

let LINEAR_INTERIOR_IMAGE_SUBSET = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
       ==> interior(IMAGE f s) SUBSET IMAGE f (interior s)`,
  MESON_TAC[INTERIOR_IMAGE_SUBSET; LINEAR_CONTINUOUS_AT]);;

let LINEAR_IMAGE_SUBSET_INTERIOR = prove
 (`!f:real^M->real^N s.
        linear f /\ (!y. ?x. f x = y)
        ==> IMAGE f (interior s) SUBSET interior(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN
  ASM_SIMP_TAC[OPEN_SURJECTIVE_LINEAR_IMAGE; OPEN_INTERIOR;
               IMAGE_SUBSET; INTERIOR_SUBSET]);;

let INTERIOR_BIJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> interior(IMAGE f s) = IMAGE f (interior s)`,
  REWRITE_TAC[interior] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [INTERIOR_BIJECTIVE_LINEAR_IMAGE];;

let FRONTIER_BIJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> frontier(IMAGE f s) = IMAGE f (frontier s)`,
  REWRITE_TAC[frontier] THEN GEOM_TRANSFORM_TAC[]);;

add_linear_invariants [FRONTIER_BIJECTIVE_LINEAR_IMAGE];;

(* ------------------------------------------------------------------------- *)
(* Corollaries, reformulations and special cases for M = N.                  *)
(* ------------------------------------------------------------------------- *)

let IN_INTERIOR_LINEAR_IMAGE = prove
 (`!f:real^M->real^N g s x.
        linear f /\ linear g /\ (f o g = I) /\ x IN interior s
        ==> (f x) IN interior (IMAGE f s)`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`]
    LINEAR_IMAGE_SUBSET_INTERIOR) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  ASM_MESON_TAC[]);;

let LINEAR_OPEN_MAPPING = prove
 (`!f:real^M->real^N g.
        linear f /\ linear g /\ (f o g = I)
        ==> !s. open s ==> open(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC OPEN_SURJECTIVE_LINEAR_IMAGE THEN
  ASM_MESON_TAC[]);;

let INTERIOR_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> interior(IMAGE f s) = IMAGE f (interior s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERIOR_BIJECTIVE_LINEAR_IMAGE THEN
  ASM_MESON_TAC[LINEAR_INJECTIVE_IMP_SURJECTIVE]);;

let INTERIOR_SURJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ (!y. ?x. f x = y)
        ==> interior(IMAGE f s) = IMAGE f (interior s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERIOR_BIJECTIVE_LINEAR_IMAGE THEN
  ASM_MESON_TAC[LINEAR_SURJECTIVE_IMP_INJECTIVE]);;

let CLOSURE_SURJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ (!y. ?x. f x = y)
        ==> closure(IMAGE f s) = IMAGE f (closure s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_INJECTIVE_LINEAR_IMAGE THEN
  ASM_MESON_TAC[LINEAR_SURJECTIVE_IMP_INJECTIVE]);;

let FRONTIER_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> frontier(IMAGE f s) = IMAGE f (frontier s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRONTIER_BIJECTIVE_LINEAR_IMAGE THEN
  ASM_MESON_TAC[LINEAR_INJECTIVE_IMP_SURJECTIVE]);;

let FRONTIER_SURJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N.
        linear f /\ (!y. ?x. f x = y)
        ==> frontier(IMAGE f s) = IMAGE f (frontier s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRONTIER_BIJECTIVE_LINEAR_IMAGE THEN
  ASM_MESON_TAC[LINEAR_SURJECTIVE_IMP_INJECTIVE]);;

let COMPLETE_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> !s. complete s ==> complete(IMAGE f s)`,
  REWRITE_TAC[COMPLETE_EQ_CLOSED; CLOSED_INJECTIVE_LINEAR_IMAGE]);;

let COMPLETE_INJECTIVE_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (complete(IMAGE f s) <=> complete s)`,
  REWRITE_TAC[COMPLETE_EQ_CLOSED; CLOSED_INJECTIVE_LINEAR_IMAGE_EQ]);;

add_linear_invariants [COMPLETE_INJECTIVE_LINEAR_IMAGE_EQ];;

let LIMPT_INJECTIVE_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((f x) limit_point_of (IMAGE f s) <=> x limit_point_of s)`,
  REWRITE_TAC[LIMPT_APPROACHABLE; EXISTS_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THENL
   [MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_BOUNDED_BELOW_POS);
    MP_TAC(ISPEC `f:real^M->real^N` LINEAR_BOUNDED_POS)] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `e * B:real`);
    FIRST_X_ASSUM(MP_TAC o SPEC `e / B:real`)] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; dist; GSYM LINEAR_SUB] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN
         CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b < x ==> a < x`) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ]);;

add_linear_invariants [LIMPT_INJECTIVE_LINEAR_IMAGE_EQ];;

let LIMPT_TRANSLATION_EQ = prove
 (`!a s x. (a + x) limit_point_of (IMAGE (\y. a + y) s) <=> x limit_point_of s`,
  REWRITE_TAC[limit_point_of] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [LIMPT_TRANSLATION_EQ];;

let OPEN_OPEN_LEFT_PROJECTION = prove
 (`!s t:real^(M,N)finite_sum->bool.
        open s /\ open t ==> open {x | x IN s /\ ?y. pastecart x y IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN s /\ ?y. (pastecart x y:real^(M,N)finite_sum) IN t} =
    s INTER IMAGE fstcart t`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_IMAGE] THEN
    MESON_TAC[FSTCART_PASTECART; PASTECART_FST_SND];
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]
      OPEN_SURJECTIVE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_FSTCART] THEN MESON_TAC[FSTCART_PASTECART]]);;

let OPEN_OPEN_RIGHT_PROJECTION = prove
 (`!s t:real^(M,N)finite_sum->bool.
        open s /\ open t ==> open {y | y IN s /\ ?x. pastecart x y IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{y | y IN s /\ ?x. (pastecart x y:real^(M,N)finite_sum) IN t} =
    s INTER IMAGE sndcart t`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_IMAGE] THEN
    MESON_TAC[SNDCART_PASTECART; PASTECART_FST_SND];
    MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]
      OPEN_SURJECTIVE_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[LINEAR_SNDCART] THEN MESON_TAC[SNDCART_PASTECART]]);;

(* ------------------------------------------------------------------------- *)
(* Even more special cases.                                                  *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_NEGATIONS = prove
 (`!s. interior(IMAGE (--) s) = IMAGE (--) (interior s)`,
  GEN_TAC THEN MATCH_MP_TAC INTERIOR_INJECTIVE_LINEAR_IMAGE THEN
  REWRITE_TAC[linear] THEN REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC);;

let SYMMETRIC_INTERIOR = prove
 (`!s:real^N->bool.
        (!x. x IN s ==> --x IN s)
        ==> !x. x IN interior s ==> (--x) IN interior s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP(ISPEC `(--):real^N->real^N` FUN_IN_IMAGE)) THEN
  REWRITE_TAC[GSYM INTERIOR_NEGATIONS] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[VECTOR_NEG_NEG]);;

let CLOSURE_NEGATIONS = prove
 (`!s. closure(IMAGE (--) s) = IMAGE (--) (closure s)`,
  GEN_TAC THEN MATCH_MP_TAC CLOSURE_INJECTIVE_LINEAR_IMAGE THEN
  REWRITE_TAC[linear] THEN REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC);;

let SYMMETRIC_CLOSURE = prove
 (`!s:real^N->bool.
        (!x. x IN s ==> --x IN s)
        ==> !x. x IN closure s ==> (--x) IN closure s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP(ISPEC `(--):real^N->real^N` FUN_IN_IMAGE)) THEN
  REWRITE_TAC[GSYM CLOSURE_NEGATIONS] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[VECTOR_NEG_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Some properties of a canonical subspace.                                  *)
(* ------------------------------------------------------------------------- *)

let SUBSPACE_SUBSTANDARD = prove
 (`!d. subspace
         {x:real^N | !i. d < i /\ i <= dimindex(:N) ==> x$i = &0}`,
  GEN_TAC THEN ASM_CASES_TAC `d <= dimindex(:N)` THENL
   [MP_TAC(ARITH_RULE `!i. d < i ==> 1 <= i`) THEN
    SIMP_TAC[subspace; IN_ELIM_THM; REAL_MUL_RZERO; REAL_ADD_LID;
             VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT];
    ASM_SIMP_TAC[ARITH_RULE `~(d:num <= e) ==> (d < i /\ i <= e <=> F)`] THEN
    REWRITE_TAC[SET_RULE `{x | T} = UNIV`; SUBSPACE_UNIV]]);;

let CLOSED_SUBSTANDARD = prove
 (`!d. closed
        {x:real^N | !i. d < i /\ i <= dimindex(:N) ==> x$i = &0}`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `{x:real^N | !i. d < i /\ i <= dimindex(:N) ==> x$i = &0} =
    INTERS {{x | basis i dot x = &0} | d < i /\ i <= dimindex(:N)}`
  SUBST1_TAC THENL
   [ALL_TAC;
    SIMP_TAC[CLOSED_INTERS; CLOSED_HYPERPLANE; IN_ELIM_THM;
             LEFT_IMP_EXISTS_THM]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN
  MP_TAC(ARITH_RULE `!i. d < i ==> 1 <= i`) THEN
  SIMP_TAC[DOT_BASIS] THEN MESON_TAC[]);;

let DIM_SUBSTANDARD = prove
 (`!d. d <= dimindex(:N)
       ==> (dim {x:real^N | !i. d < i /\ i <= dimindex(:N)
                                ==> x$i = &0} =
            d)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIM_UNIQUE THEN
  EXISTS_TAC `IMAGE (basis:num->real^N) (1..d)` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    MESON_TAC[BASIS_COMPONENT; ARITH_RULE `d < i ==> 1 <= i`; NOT_LT];
    ALL_TAC;
    MATCH_MP_TAC INDEPENDENT_MONO THEN
    EXISTS_TAC `{basis i :real^N | 1 <= i /\ i <= dimindex(:N)}` THEN
    REWRITE_TAC[INDEPENDENT_STDBASIS]THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    ASM_MESON_TAC[LE_TRANS];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_MESON_TAC[LE_TRANS; BASIS_INJ]] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `0 < i <=> 1 <= i`; SPAN_STDBASIS] THEN
    SUBGOAL_THEN `IMAGE basis (1 .. 0) :real^N->bool = {}` SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_EQ_EMPTY; NUMSEG_EMPTY; ARITH]; ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[SPAN_EMPTY; SUBSET; IN_ELIM_THM; IN_SING] THEN
    SIMP_TAC[CART_EQ; VEC_COMPONENT];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC d <= n ==> d <= n`] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_TAC THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x - (x$(SUC d)) % basis(SUC d) :real^N`) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP(ARITH_RULE `d < i ==> 1 <= i`)) THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[BASIS_COMPONENT] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; REAL_SUB_REFL] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
    ASM_MESON_TAC[ARITH_RULE `d < i /\ ~(i = SUC d) ==> SUC d < i`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBST1_TAC(VECTOR_ARITH
   `x = (x - (x$(SUC d)) % basis(SUC d)) +
        x$(SUC d) % basis(SUC d) :real^N`) THEN
  MATCH_MP_TAC SPAN_ADD THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SPAN_MONO; SUBSET_IMAGE; SUBSET; SUBSET_NUMSEG; LE_REFL; LE];
    MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN
    MESON_TAC[LE_REFL; ARITH_RULE `1 <= SUC d`]]);;

(* ------------------------------------------------------------------------- *)
(* Hence closure and completeness of all subspaces.                          *)
(* ------------------------------------------------------------------------- *)

let CLOSED_SUBSPACE = prove
 (`!s:real^N->bool. subspace s ==> closed s`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `d = dim(s:real^N->bool)` THEN
  MP_TAC(MATCH_MP DIM_SUBSTANDARD
    (ISPEC `s:real^N->bool` DIM_SUBSET_UNIV)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`{x:real^N | !i. d < i /\ i <= dimindex(:N)
                                ==> x$i = &0}`;
    `s:real^N->bool`] SUBSPACE_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[SUBSPACE_SUBSTANDARD] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(ISPEC `f:real^N->real^N` CLOSED_INJECTIVE_IMAGE_SUBSPACE) THEN
  ASM_REWRITE_TAC[SUBSPACE_SUBSTANDARD; CLOSED_SUBSTANDARD] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[LINEAR_0]] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[VEC_COMPONENT; ARITH_RULE `d < i ==> 1 <= i`]);;

let COMPLETE_SUBSPACE = prove
 (`!s:real^N->bool. subspace s ==> complete s`,
  REWRITE_TAC[COMPLETE_EQ_CLOSED; CLOSED_SUBSPACE]);;

let CLOSED_SPAN = prove
 (`!s. closed(span s)`,
  SIMP_TAC[CLOSED_SUBSPACE; SUBSPACE_SPAN]);;

let DIM_CLOSURE = prove
 (`!s:real^N->bool. dim(closure s) = dim s`,
  GEN_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM DIM_SPAN]; ALL_TAC] THEN
  MATCH_MP_TAC DIM_SUBSET THEN REWRITE_TAC[CLOSURE_SUBSET] THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN
  SIMP_TAC[CLOSED_SUBSPACE; SUBSPACE_SPAN; SPAN_INC]);;

let CLOSED_BOUNDEDPREIM_CONTINUOUS_IMAGE = prove
 (`!f:real^M->real^N s.
      closed s /\ f continuous_on s /\
      (!e. bounded {x | x IN s /\ norm(f x) <= e})
      ==> closed(IMAGE f s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSED_INTERS_COMPACT] THEN
  REWRITE_TAC[SET_RULE
   `cball(vec 0,e) INTER IMAGE (f:real^M->real^N) s =
    IMAGE f (s INTER {x | x IN s /\ f x IN cball(vec 0,e)})`] THEN
  X_GEN_TAC `e:real` THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_CBALL_0];
      ASM_SIMP_TAC[CONTINUOUS_CLOSED_PREIMAGE; CLOSED_CBALL]]]);;

let CLOSED_INJECTIVE_IMAGE_SUBSET_SUBSPACE = prove
 (`!f:real^M->real^N s t.
        closed s /\ s SUBSET t /\ subspace t /\
        linear f /\
        (!x. x IN t /\ f(x) = vec 0 ==> x = vec 0)
        ==> closed(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_BOUNDEDPREIM_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON] THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `t:real^M->bool`]
    INJECTIVE_IMP_ISOMETRIC) THEN
  ASM_SIMP_TAC[CLOSED_SUBSPACE; real_ge] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `e:real` THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `cball(vec 0:real^M,e / B)` THEN
  REWRITE_TAC[BOUNDED_CBALL] THEN
  ASM_SIMP_TAC[SUBSET; IN_ELIM_THM; IN_CBALL_0; REAL_LE_RDIV_EQ] THEN
  ASM_MESON_TAC[SUBSET; REAL_LE_TRANS]);;

let BASIS_COORDINATES_LIPSCHITZ = prove
 (`!b:real^N->bool.
        independent b
        ==> ?B. &0 < B /\
                !c v. v IN b
                      ==> abs(c v) <= B * norm(vsum b (\v. c(v) % v))`,
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INDEPENDENT_BOUND) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b:num->real^N` STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ABBREV_TAC `n = CARD(k:real^N->bool)` THEN
  MP_TAC(ISPECL
   [`(\x. vsum(1..n) (\i. x$i % b i)):real^N->real^N`;
    `span(IMAGE basis (1..n)):real^N->bool`]
        INJECTIVE_IMP_ISOMETRIC) THEN
  REWRITE_TAC[SUBSPACE_SPAN] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [SIMP_TAC[CLOSED_SUBSPACE; SUBSPACE_SPAN]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC LINEAR_VMUL_COMPONENT THEN
      SIMP_TAC[LINEAR_ID] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SPAN_IMAGE_BASIS]) THEN
    REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
    DISCH_THEN(X_CHOOSE_TAC `c:real^N->num`) THEN
    SUBGOAL_THEN
     `vsum(1..n) (\i. (x:real^N)$i % b i:real^N) = vsum k (\v. x$(c v) % v)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN
      MAP_EVERY EXISTS_TAC [`b:num->real^N`; `c:real^N->num`] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INDEPENDENT_EXPLICIT]) THEN
    DISCH_THEN(MP_TAC o SPEC `\v:real^N. (x:real^N)$(c v)` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; FORALL_IN_IMAGE; VEC_COMPONENT] THEN
    ASM_MESON_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `inv(B:real)` THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N->real`; `j:num`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `inv B * x = x / B`] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o rand o rand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `(lambda i. if 1 <= i /\ i <= n then c(b i:real^N) else &0):real^N`) THEN
  SIMP_TAC[IN_SPAN_IMAGE_BASIS; LAMBDA_BETA] THEN
  ANTS_TAC THENL [MESON_TAC[IN_NUMSEG]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = v /\ u <= y ==> x >= y ==> u <= v`) THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    SUBGOAL_THEN `!i. i <= n ==> i <= dimindex(:N)` MP_TAC THENL
     [ASM_ARITH_TAC; SIMP_TAC[LAMBDA_BETA] THEN DISCH_THEN(K ALL_TAC)] THEN
    REWRITE_TAC[o_THM];
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN
    MP_TAC(ISPECL
     [`(lambda i. if 1 <= i /\ i <= n then c(b i:real^N) else &0):real^N`;
      `j:num`] COMPONENT_LE_NORM) THEN
    SUBGOAL_THEN `1 <= j /\ j <= dimindex(:N)` MP_TAC THENL
     [ASM_ARITH_TAC; SIMP_TAC[LAMBDA_BETA] THEN ASM_REWRITE_TAC[]]]);;

let BASIS_COORDINATES_CONTINUOUS = prove
 (`!b:real^N->bool e.
        independent b /\ &0 < e
        ==> ?d. &0 < d /\
                !c. norm(vsum b (\v. c(v) % v)) < d
                    ==> !v. v IN b ==> abs(c v) < e`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BASIS_COORDINATES_LIPSCHITZ) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / B:real` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
  X_GEN_TAC `c:real^N->real` THEN DISCH_TAC THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `B * norm(vsum b (\v:real^N. c v % v))` THEN
  ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Affine transformations of intervals.                                      *)
(* ------------------------------------------------------------------------- *)

let AFFINITY_INVERSES = prove
 (`!m c. ~(m = &0)
         ==> (\x. m % x + c) o (\x. inv(m) % x + (--(inv(m) % c))) = I /\
             (\x. inv(m) % x + (--(inv(m) % c))) o (\x. m % x + c) = I`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_RNEG] THEN
  SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RINV] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let REAL_AFFINITY_LE = prove
 (`!m c x y. &0 < m ==> (m * x + c <= y <=> x <= inv(m) * y + --(c / m))`,
  REWRITE_TAC[REAL_ARITH `m * x + c <= y <=> x * m <= y - c`] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC);;

let REAL_LE_AFFINITY = prove
 (`!m c x y. &0 < m ==> (y <= m * x + c <=> inv(m) * y + --(c / m) <= x)`,
  REWRITE_TAC[REAL_ARITH `y <= m * x + c <=> y - c <= x * m`] THEN
  SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

let REAL_AFFINITY_LT = prove
 (`!m c x y. &0 < m ==> (m * x + c < y <=> x < inv(m) * y + --(c / m))`,
  SIMP_TAC[REAL_LE_AFFINITY; GSYM REAL_NOT_LE]);;

let REAL_LT_AFFINITY = prove
 (`!m c x y. &0 < m ==> (y < m * x + c <=> inv(m) * y + --(c / m) < x)`,
  SIMP_TAC[REAL_AFFINITY_LE; GSYM REAL_NOT_LE]);;

let REAL_AFFINITY_EQ = prove
 (`!m c x y. ~(m = &0) ==> (m * x + c = y <=> x = inv(m) * y + --(c / m))`,
  CONV_TAC REAL_FIELD);;

let REAL_EQ_AFFINITY = prove
 (`!m c x y. ~(m = &0) ==> (y = m * x + c  <=> inv(m) * y + --(c / m) = x)`,
  CONV_TAC REAL_FIELD);;

let VECTOR_AFFINITY_EQ = prove
 (`!m c x y. ~(m = &0)
             ==> (m % x + c = y <=> x = inv(m) % y + --(inv(m) % c))`,
  SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           real_div; VECTOR_NEG_COMPONENT; REAL_AFFINITY_EQ] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let VECTOR_EQ_AFFINITY = prove
 (`!m c x y. ~(m = &0)
             ==> (y = m % x + c <=> inv(m) % y + --(inv(m) % c) = x)`,
  SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           real_div; VECTOR_NEG_COMPONENT; REAL_EQ_AFFINITY] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let IMAGE_AFFINITY_INTERVAL = prove
 (`!a b:real^N m c.
        IMAGE (\x. m % x + c) (interval[a,b]) =
            if interval[a,b] = {} then {}
            else if &0 <= m then interval[m % a + c,m % b + c]
            else interval[m % b + c,m % a + c]`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  ASM_CASES_TAC `m = &0` THEN ASM_REWRITE_TAC[REAL_LE_LT] THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; COND_ID] THEN
    REWRITE_TAC[INTERVAL_SING] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `~(x = &0) ==> &0 < x \/ &0 < --x`)) THEN
  ASM_SIMP_TAC[EXTENSION; IN_IMAGE; REAL_ARITH `&0 < --x ==> ~(&0 < x)`] THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[VECTOR_ARITH `x = m % y + c <=> c = (--m) % y + x`]] THEN
  ASM_SIMP_TAC[VECTOR_EQ_AFFINITY; REAL_LT_IMP_NZ; UNWIND_THM1] THEN
  SIMP_TAC[IN_INTERVAL; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           VECTOR_NEG_COMPONENT] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_LT_INV_EQ]) THEN
  SIMP_TAC[REAL_AFFINITY_LE; REAL_LE_AFFINITY; real_div] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[REAL_INV_INV] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_NEGNEG] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < m ==> (inv m * x) * m = x`] THEN
  GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Existence of eigenvectors. The proof is only in this file because it uses *)
(* a few simple results about continuous functions (at least                 *)
(* CONTINUOUS_ON_LIFT_DOT2, CONTINUOUS_ATTAINS_SUP and CLOSED_SUBSPACE).     *)
(* ------------------------------------------------------------------------- *)

let SELF_ADJOINT_HAS_EIGENVECTOR_IN_SUBSPACE = prove
 (`!f:real^N->real^N s.
        linear f /\ adjoint f = f /\
        subspace s /\ ~(s = {vec 0}) /\ (!x. x IN s ==> f x IN s)
        ==> ?v c. v IN s /\ norm(v) = &1 /\ f(v) = c % v`,
  let lemma = prove
   (`!a b. (!x. a * x <= b * x pow 2) ==> &0 <= b ==> a = &0`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN
    ASM_CASES_TAC `b = &0` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(fun t -> MP_TAC(SPEC `&1` t) THEN
        MP_TAC(SPEC `-- &1` t)) THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN  FIRST_X_ASSUM(MP_TAC o SPEC `a / &2 / b`) THEN
      ASM_SIMP_TAC[REAL_FIELD
       `&0 < b ==> (b * (a / b) pow 2) = a pow 2 / b`] THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN SIMP_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
      REWRITE_TAC[REAL_LT_SQUARE; REAL_ARITH
        `(a * a) / &2 <= (a / &2) pow 2 <=> ~(&0 < a * a)`]]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. (f x) dot x`;
                 `s INTER sphere(vec 0:real^N,&1)`]
        CONTINUOUS_ATTAINS_SUP) THEN
  REWRITE_TAC[EXISTS_IN_GSPEC; FORALL_IN_GSPEC; o_DEF] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_DOT2; LINEAR_CONTINUOUS_ON;
                   CONTINUOUS_ON_ID] THEN
    ASM_SIMP_TAC[COMPACT_SPHERE; CLOSED_INTER_COMPACT; CLOSED_SUBSPACE] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
      `~(s = {a}) ==> a IN s ==> ?b. ~(b = a) /\ b IN s`)) THEN
    ASM_SIMP_TAC[SUBSPACE_0; IN_SPHERE_0; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `inv(norm x) % x:real^N` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; VECTOR_SUB_RZERO; NORM_MUL] THEN
    ASM_SIMP_TAC[SUBSPACE_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_SPHERE_0] THEN STRIP_TAC THEN
    ABBREV_TAC `c = (f:real^N->real^N) v dot v` THEN
    EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `p = \x y:real^N. c * (x dot y) - (f x) dot y` THEN
  SUBGOAL_THEN `!x:real^N. x IN s ==> &0 <= p x x` (LABEL_TAC "POSDEF") THENL
   [X_GEN_TAC `x:real^N` THEN EXPAND_TAC "p" THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `x:real^N = vec 0` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[DOT_RZERO; REAL_MUL_RZERO; REAL_SUB_LE; REAL_LE_REFL] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `inv(norm x) % x:real^N`) THEN
    ASM_SIMP_TAC[SUBSPACE_MUL] THEN
    ASM_SIMP_TAC[LINEAR_CMUL; NORM_MUL; REAL_ABS_INV; DOT_RMUL] THEN
    ASM_SIMP_TAC[REAL_ABS_NORM; REAL_MUL_LINV; NORM_EQ_0; DOT_LMUL] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; DOT_POS_LT] THEN
    REWRITE_TAC[GSYM NORM_POW_2; real_div; REAL_INV_POW] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN s ==> !a. p v y * a <= p y y * a pow 2`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    REMOVE_THEN "POSDEF" (MP_TAC o SPEC `v - (&2 * a) % y:real^N`) THEN
    EXPAND_TAC "p" THEN ASM_SIMP_TAC[SUBSPACE_SUB; SUBSPACE_MUL] THEN
    ASM_SIMP_TAC[LINEAR_SUB; LINEAR_CMUL] THEN
    REWRITE_TAC[DOT_LSUB; DOT_LMUL] THEN
    REWRITE_TAC[DOT_RSUB; DOT_RMUL] THEN
    SUBGOAL_THEN `f y dot (v:real^N) = f v dot y` SUBST1_TAC THENL
     [ASM_MESON_TAC[ADJOINT_CLAUSES; DOT_SYM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM NORM_POW_2] THEN REWRITE_TAC[NORM_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH
        `&4 * (z - y) = x ==> &0 <= x ==> y <= z`) THEN
    REWRITE_TAC[DOT_SYM] THEN CONV_TAC REAL_RING;
    DISCH_THEN(MP_TAC o GEN `y:real^N` o DISCH `(y:real^N) IN s` o
      MATCH_MP lemma o C MP (ASSUME `(y:real^N) IN s`) o SPEC `y:real^N`) THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "p" THEN
    REWRITE_TAC[GSYM DOT_LMUL; GSYM DOT_LSUB] THEN
    DISCH_THEN(MP_TAC o SPEC `c % v - f v:real^N`) THEN
    ASM_SIMP_TAC[SUBSPACE_MUL; SUBSPACE_SUB; DOT_EQ_0; VECTOR_SUB_EQ]]);;

let SELF_ADJOINT_HAS_EIGENVECTOR = prove
 (`!f:real^N->real^N.
        linear f /\ adjoint f = f ==> ?v c. norm(v) = &1 /\ f(v) = c % v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `(:real^N)`]
        SELF_ADJOINT_HAS_EIGENVECTOR_IN_SUBSPACE) THEN
  ASM_REWRITE_TAC[SUBSPACE_UNIV; IN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!a. ~(a IN s) ==> ~(UNIV = s)`) THEN
  EXISTS_TAC `vec 1:real^N` THEN
  REWRITE_TAC[IN_SING; VEC_EQ; ARITH_EQ]);;

let SELF_ADJOINT_HAS_EIGENVECTOR_BASIS_OF_SUBSPACE = prove
 (`!f:real^N->real^N s.
        linear f /\ adjoint f = f /\
        subspace s /\ (!x. x IN s ==> f x IN s)
        ==> ?b. b SUBSET s /\
                pairwise orthogonal b /\
                (!x. x IN b ==> norm x = &1 /\ ?c. f(x) = c % x) /\
                independent b /\
                span b = s /\
                b HAS_SIZE dim s`,
  let lemma = prove
   (`!f:real^N->real^N s.
          linear f /\ adjoint f = f /\ subspace s /\ (!x. x IN s ==> f x IN s)
          ==> ?b. b SUBSET s /\ b HAS_SIZE dim s /\
                  pairwise orthogonal b /\
                  (!x. x IN b ==> norm x = &1 /\ ?c. f(x) = c % x)`,
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REWRITE_TAC[IMP_IMP] THEN
    GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
    WF_INDUCT_TAC `dim(s:real^N->bool)` THEN STRIP_TAC THEN
    ASM_CASES_TAC `dim(s:real^N->bool) = 0` THENL
     [EXISTS_TAC `{}:real^N->bool` THEN
      ASM_SIMP_TAC[HAS_SIZE_CLAUSES; NOT_IN_EMPTY;
                   PAIRWISE_EMPTY; EMPTY_SUBSET];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [DIM_EQ_0]) THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP (SET_RULE
     `~(s SUBSET {a}) ==> ~(s = {a})`)) THEN
    MP_TAC(ISPECL [`f:real^N->real^N`; `s:real^N->bool`]
      SELF_ADJOINT_HAS_EIGENVECTOR_IN_SUBSPACE) THEN
    ASM_REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` MP_TAC) THEN
    ASM_CASES_TAC `v:real^N = vec 0` THEN ASM_REWRITE_TAC[NORM_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{y:real^N | y IN s /\ orthogonal v y}`) THEN
    REWRITE_TAC[SUBSPACE_ORTHOGONAL_TO_VECTOR; IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`span {v:real^N}`; `s:real^N->bool`]
          DIM_SUBSPACE_ORTHOGONAL_TO_VECTORS) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ORTHOGONAL_SYM] ORTHOGONAL_TO_SPAN_EQ] THEN
    ASM_REWRITE_TAC[SUBSPACE_SPAN; IN_SING; FORALL_UNWIND_THM2] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN ASM SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[DIM_SPAN; DIM_SING; ARITH_RULE `n < n + 1`] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER {x | P x}`] THEN
      ASM_SIMP_TAC[SUBSPACE_INTER; SUBSPACE_ORTHOGONAL_TO_VECTOR] THEN
      REWRITE_TAC[orthogonal] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `(f:real^N->real^N) v dot x` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[ADJOINT_CLAUSES];
        ASM_MESON_TAC[DOT_LMUL; REAL_MUL_RZERO]];
      DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(v:real^N) INSERT b` THEN
      ASM_REWRITE_TAC[FORALL_IN_INSERT] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[PAIRWISE_INSERT] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE; SUBSET; IN_ELIM_THM]) THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[HAS_SIZE; FINITE_INSERT; CARD_CLAUSES] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD1] THEN
        ASM_MESON_TAC[ORTHOGONAL_REFL];
        RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
        ASM_MESON_TAC[ORTHOGONAL_SYM]]]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `s:real^N->bool`] lemma) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `b:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
    ASM_MESON_TAC[NORM_ARITH `~(norm(vec 0:real^N) = &1)`];
    DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SPAN_SUBSET_SUBSPACE];
      MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
      RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
      ASM_REWRITE_TAC[LE_REFL]]]);;

let SELF_ADJOINT_HAS_EIGENVECTOR_BASIS = prove
 (`!f:real^N->real^N.
        linear f /\ adjoint f = f
        ==> ?b. pairwise orthogonal b /\
                (!x. x IN b ==> norm x = &1 /\ ?c. f(x) = c % x) /\
                independent b /\
                span b = (:real^N) /\
                b HAS_SIZE (dimindex(:N))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^N->real^N`; `(:real^N)`]
        SELF_ADJOINT_HAS_EIGENVECTOR_BASIS_OF_SUBSPACE) THEN
  ASM_REWRITE_TAC[SUBSPACE_UNIV; IN_UNIV; DIM_UNIV; SUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Diagonalization of symmetric matrix.                                      *)
(* ------------------------------------------------------------------------- *)

let SYMMETRIC_MATRIX_DIAGONALIZABLE_EXPLICIT = prove
 (`!A:real^N^N.
    transp A = A
    ==> ?P d. orthogonal_matrix P /\
              transp P ** A ** P = (lambda i j. if i = j then d i else &0)`,
  let lemma1 = prove
   (`!A:real^N^N P:real^N^N d.
       A ** P = P ** (lambda i j. if i = j then d i else &0) <=>
       !i. 1 <= i /\ i <= dimindex(:N)
           ==> A ** column i P = d i % column i P`,
    SIMP_TAC[CART_EQ; matrix_mul; matrix_vector_mul; LAMBDA_BETA;
             column; VECTOR_MUL_COMPONENT] THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[REAL_MUL_RZERO; SUM_DELTA; IN_NUMSEG] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[REAL_MUL_SYM]) in
  let lemma2 = prove
   (`!A:real^N^N P:real^N^N d.
          orthogonal_matrix P /\
          transp P ** A ** P = (lambda i j. if i = j then d i else &0) <=>
          orthogonal_matrix P /\
          !i. 1 <= i /\ i <= dimindex(:N)
              ==> A ** column i P = d i % column i P`,
    REPEAT GEN_TAC THEN REWRITE_TAC[GSYM lemma1; orthogonal_matrix] THEN
    ABBREV_TAC `D:real^N^N = lambda i j. if i = j then d i else &0` THEN
    MESON_TAC[MATRIX_MUL_ASSOC; MATRIX_MUL_LID]) in
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[lemma2] THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN
  MP_TAC(ISPEC `\x:real^N. (A:real^N^N) ** x`
    SELF_ADJOINT_HAS_EIGENVECTOR_BASIS) THEN
  ASM_SIMP_TAC[MATRIX_SELF_ADJOINT; MATRIX_VECTOR_MUL_LINEAR;
               MATRIX_OF_MATRIX_VECTOR_MUL] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` MP_TAC) THEN
  REWRITE_TAC[CONJ_ASSOC] THEN ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN
  REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
  ASM_REWRITE_TAC[IN_NUMSEG; TAUT
   `p /\ q /\ x = y ==> a = b <=> p /\ q /\ ~(a = b) ==> ~(x = y)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^N` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[PAIRWISE_IMAGE; FORALL_IN_IMAGE] THEN
  ASM_SIMP_TAC[pairwise; IN_NUMSEG] THEN STRIP_TAC THEN
  EXISTS_TAC `transp(lambda i. f i):real^N^N` THEN
  SIMP_TAC[COLUMN_TRANSP; ORTHOGONAL_MATRIX_TRANSP] THEN
  SIMP_TAC[ORTHOGONAL_MATRIX_ORTHONORMAL_ROWS_INDEXED; row] THEN
  SIMP_TAC[LAMBDA_ETA; LAMBDA_BETA; pairwise; IN_NUMSEG] THEN
  ASM_MESON_TAC[]);;

let SYMMETRIC_MATRIX_IMP_DIAGONALIZABLE = prove
 (`!A:real^N^N.
     transp A = A
     ==> ?P. orthogonal_matrix P /\ diagonal_matrix(transp P ** A ** P)`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SYMMETRIC_MATRIX_DIAGONALIZABLE_EXPLICIT) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[diagonal_matrix; LAMBDA_BETA]);;

let SYMMETRIC_MATRIX_EQ_DIAGONALIZABLE = prove
 (`!A:real^N^N.
     transp A = A <=>
     ?P. orthogonal_matrix P /\ diagonal_matrix(transp P ** A ** P)`,
  GEN_TAC THEN EQ_TAC THEN
  REWRITE_TAC[SYMMETRIC_MATRIX_IMP_DIAGONALIZABLE] THEN
  REWRITE_TAC[orthogonal_matrix] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^N^N` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `D:real^N^N = transp P ** (A:real^N^N) ** P` THEN
  SUBGOAL_THEN `A:real^N^N = P ** (D:real^N^N) ** transp P` SUBST1_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[MATRIX_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[MATRIX_MUL_LID] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_MUL_ASSOC; MATRIX_MUL_RID];
    REWRITE_TAC[MATRIX_TRANSP_MUL; TRANSP_TRANSP; MATRIX_MUL_ASSOC] THEN
    ASM_MESON_TAC[TRANSP_DIAGONAL_MATRIX]]);;
