(* ========================================================================= *)
(* Elementary topology in Euclidean space.                                   *)
(* ========================================================================= *)

parse_as_infix ("open_in",(12,"right"));;
parse_as_infix ("closed_in",(12,"right"));;

let open_in = new_definition
  `s open_in u <=>
        s SUBSET u /\
        !x. x IN s ==> ?e. &0 < e /\
                           !x'. x' IN u /\ dist(x',x) < e ==> x' IN s`;;

let closed_in = new_definition
  `s closed_in u <=> s SUBSET u /\ (u DIFF s) open_in u`;;

let OPEN_IN_SUBSET = prove
 (`!s u. s open_in u ==> s SUBSET u`,
  SIMP_TAC[open_in]);;

let OPEN_IN_EMPTY = prove
 (`!u. {} open_in u`,
  REWRITE_TAC[open_in; EMPTY_SUBSET; NOT_IN_EMPTY]);;

let OPEN_IN_REFL = prove
 (`!u. u open_in u`,
  SIMP_TAC[open_in; SUBSET_REFL] THEN MESON_TAC[REAL_LT_01]);;

let OPEN_IN_UNIONS = prove
 (`!u. (!s. s IN f ==> s open_in u) ==> (UNIONS f) open_in u`,
  REWRITE_TAC[open_in; SUBSET; IN_UNIONS] THEN MESON_TAC[]);;

let OPEN_IN_UNION = prove
 (`!s t u. s open_in u /\ t open_in u ==> (s UNION t) open_in u`,
  REWRITE_TAC[open_in; IN_UNION; SUBSET] THEN MESON_TAC[]);;

let OPEN_IN_INTER = prove
 (`!s t u. s open_in u /\ t open_in u ==> (s INTER t) open_in u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[open_in; IN_INTER] THEN MATCH_MP_TAC(TAUT
   `(a /\ c ==> e) /\ (b /\ d ==> f) ==> (a /\ b) /\ (c /\ d) ==> e /\ f`) THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `d1:real`) (X_CHOOSE_TAC `d2:real`)) THEN
  MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN
  ASM_MESON_TAC[REAL_LT_TRANS]);;

let OPEN_IN_SUBOPEN = prove
 (`!s u. s open_in u <=>
         !x. x IN s ==> ?t. t open_in u /\ x IN t /\ t SUBSET s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[SUBSET_REFL]; REWRITE_TAC[open_in; SUBSET] THEN MESON_TAC[]]);;

let CLOSED_IN_SUBSET = prove
 (`!s u. s closed_in u ==> s SUBSET u`,
  SIMP_TAC[closed_in]);;

let CLOSED_IN_EMPTY = prove
 (`!u. {} closed_in u`,
  REWRITE_TAC[closed_in; EMPTY_SUBSET; DIFF_EMPTY; OPEN_IN_REFL]);;

let CLOSED_IN_REFL = prove
 (`!u. u closed_in u`,
  REWRITE_TAC[closed_in; SUBSET_REFL; DIFF_EQ_EMPTY; OPEN_IN_EMPTY]);;

let CLOSED_IN_UNION = prove
 (`!s t u. s closed_in u /\ t closed_in u ==> (s UNION t) closed_in u`,
  let lemma = prove
   (`s DIFF (t UNION u) = (s DIFF t) INTER (s DIFF u)`,SET_TAC[]) in
  SIMP_TAC[closed_in; lemma; OPEN_IN_INTER] THEN SET_TAC[]);;

let CLOSED_IN_INTER = prove
 (`!s t u. s closed_in u /\ t closed_in u ==> (s INTER t) closed_in u`,
  let lemma = prove
   (`s DIFF (t INTER u) = (s DIFF t) UNION (s DIFF u)`,SET_TAC[]) in
  SIMP_TAC[closed_in; lemma; OPEN_IN_UNION] THEN SET_TAC[]);;

let CLOSED_IN_INTERS = prove
 (`!u. ~(f = {}) /\ (!s. s IN f ==> s closed_in u) ==> (INTERS f) closed_in u`,
  let lemma = prove
   (`s DIFF (INTERS f) = UNIONS {t | ?u. u IN f /\ (t = s DIFF u)}`,
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_INTERS; IN_ELIM_THM] THEN
    MESON_TAC[IN_DIFF]) in
  REWRITE_TAC[closed_in; lemma] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[OPEN_IN_UNIONS; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN SET_TAC[]);;

let OPEN_IN_CLOSED_IN = prove
 (`!s u. s SUBSET u ==> (s open_in u <=> (u DIFF s) closed_in u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[closed_in; SUBSET_DIFF] THEN
  REWRITE_TAC[open_in; IN_DIFF; IN_DIFF; SUBSET] THEN MESON_TAC[]);;

let OPEN_IN_CLOSED_IN_EQ = prove
 (`!s u. s open_in u <=> s SUBSET u /\ (u DIFF s) closed_in u`,
  MESON_TAC[OPEN_IN_CLOSED_IN; OPEN_IN_SUBSET]);;

let OPEN_IN_DIFF = prove
 (`!s t u. s open_in u /\ t closed_in u ==> (s DIFF t) open_in u`,
  let lemma = prove
   (`s SUBSET u ==> ((s DIFF t) = s INTER (u DIFF t))`,SET_TAC[]) in
  SIMP_TAC[OPEN_IN_SUBSET; lemma; closed_in; OPEN_IN_INTER]);;

let CLOSED_IN_DIFF = prove
 (`!s t u. s closed_in u /\ t open_in u ==> (s DIFF t) closed_in u`,
  let lemma = prove
   (`s SUBSET u ==> ((s DIFF t) = s INTER (u DIFF t))`,SET_TAC[]) in
  SIMP_TAC[CLOSED_IN_SUBSET; lemma] THEN
  SIMP_TAC[CLOSED_IN_INTER; GSYM OPEN_IN_CLOSED_IN; OPEN_IN_SUBSET]);;



(* ------------------------------------------------------------------------- *)
(* The "universal" versions are what we use most of the time.                *)
(* ------------------------------------------------------------------------- *)

let open_def_fan = new_definition
  `open_fan s <=> !x. x IN s ==> ?e. &0 < e /\ !x'. dist(x',x) < e ==> x' IN s`;;

let closed_fan = new_definition
  `closed_fan(s:real^N->bool) <=> open_fan(UNIV DIFF s)`;;

let OPEN_IN_FAN = prove
 (`!s:real^N->bool. open_fan s <=> s open_in UNIV`,
  REWRITE_TAC[open_def_fan; open_in; SUBSET_UNIV; IN_UNIV]);;


let CLOSED_IN_FAN = prove
 (`!s:real^N->bool. closed_fan s <=> s closed_in UNIV`,
  REWRITE_TAC[closed_fan; closed_in; SUBSET_UNIV; OPEN_IN_FAN]);;

let OPEN_EMPTY_FAN = prove
 (`open_fan {}`,
  REWRITE_TAC[OPEN_IN_FAN; OPEN_IN_EMPTY]);;

let OPEN_UNIV_FAN = prove
 (`open_fan(UNIV:real^N->bool)`,
  REWRITE_TAC[OPEN_IN_FAN; OPEN_IN_REFL]);;

let OPEN_UNIONS_FAN = prove
 (`(!s. s IN f ==> open_fan s) ==> open_fan(UNIONS f)`,
  REWRITE_TAC[OPEN_IN_FAN; OPEN_IN_UNIONS]);;

let OPEN_UNION_FAN = prove
 (`!s t. open_fan s /\ open_fan t ==> open_fan(s UNION t)`,
  REWRITE_TAC[OPEN_IN_FAN; OPEN_IN_UNION]);;

let OPEN_INTER_FAN = prove
 (`!s t. open_fan s /\ open_fan t ==> open_fan(s INTER t)`,
  REWRITE_TAC[OPEN_IN_FAN; OPEN_IN_INTER]);;

let OPEN_SUBOPEN_FAN = prove
 (`!s. open_fan s <=> !x. x IN s ==> ?t. open_fan t /\ x IN t /\ t SUBSET s`, 
REWRITE_TAC[OPEN_IN_FAN; GSYM OPEN_IN_SUBOPEN]);;

let CLOSED_EMPTY_FAN = prove
 (`closed_fan {}`,
  REWRITE_TAC[CLOSED_IN_FAN; CLOSED_IN_EMPTY]);;

let CLOSED_UNIV_FAN = prove
 (`closed_fan(UNIV:real^N->bool)`,
  REWRITE_TAC[CLOSED_IN_FAN; CLOSED_IN_REFL]);;

let CLOSED_UNION_FAN = prove
 (`!s t. closed_fan s /\ closed_fan t ==> closed_fan(s UNION t)`,
  REWRITE_TAC[CLOSED_IN_FAN; CLOSED_IN_UNION]);;

let CLOSED_INTER_FAN = prove
 (`!s t. closed_fan s /\ closed_fan t ==> closed_fan(s INTER t)`,
  REWRITE_TAC[CLOSED_IN_FAN; CLOSED_IN_INTER]);;

let lemma_closed_inters_fan1 = prove
   (`s DIFF (INTERS f) = UNIONS {t | ?u. u IN f /\ (t = s DIFF u)}`,
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_INTERS; IN_ELIM_THM] THEN
    MESON_TAC[IN_DIFF]);;

let CLOSED_INTERS_FAN = prove(
`!f. (!s:real^N->bool. s IN f ==> closed_fan s) ==> closed_fan(INTERS f)`,
   REWRITE_TAC[closed_fan; lemma_closed_inters_fan1] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[OPEN_UNIONS_FAN; IN_ELIM_THM; LEFT_IMP_EXISTS_THM]);;

let OPEN_CLOSED_FAN = prove
 (`!s:real^N->bool. open_fan s <=> closed_fan(UNIV DIFF s)`,
  SIMP_TAC[OPEN_IN_FAN; CLOSED_IN_FAN; OPEN_IN_CLOSED_IN; SUBSET_UNIV]);;

let OPEN_DIFF_FAN = prove
 (`!s t. open_fan s /\ closed_fan t ==> open_fan(s DIFF t)`,
  REWRITE_TAC[OPEN_IN_FAN; CLOSED_IN_FAN; OPEN_IN_DIFF]);;

let CLOSED_DIFF_FAN = prove
 (`!s t. closed_fan s /\ open_fan t ==> closed_fan(s DIFF t)`,
  REWRITE_TAC[OPEN_IN_FAN; CLOSED_IN_FAN; CLOSED_IN_DIFF]);;

let OPEN_INTERS_FAN = prove
 (`!s. FINITE s /\ (!t. t IN s ==> open_fan t) ==> open_fan(INTERS s)`,
REWRITE_TAC[GSYM IMP_IMP] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG
  THEN REWRITE_TAC[INTERS_INSERT; INTERS_0; OPEN_UNIV_FAN; IN_INSERT] THEN
  MESON_TAC[OPEN_INTER_FAN]);;

let CLOSED_UNIONS_FAN = prove
 (`!s. FINITE s /\ (!t. t IN s ==> closed_fan t) ==> closed_fan(UNIONS s)`,
  REWRITE_TAC[GSYM IMP_IMP] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_INSERT; UNIONS_0; CLOSED_EMPTY_FAN; IN_INSERT] THEN
  MESON_TAC[CLOSED_UNION_FAN]);;



(* ------------------------------------------------------------------------- *)
(* Open balls.                                                               *)
(* ------------------------------------------------------------------------- *)


let ball_fan = new_definition
  `ball_fan(x,e) = { y | dist(x,y) < e}`;;

let IN_BALL_FAN = prove
 (`!x y e. y IN (ball_fan(x,e)) <=> dist(x,y) < e`,
  REWRITE_TAC[ball_fan; IN_ELIM_THM]);;

let OPEN_BALL_FAN = prove
 (`!x e. open_fan(ball_fan(x,e))`,
  REWRITE_TAC[open_def_fan; ball_fan; IN_ELIM_THM] 
  THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  MESON_TAC[REAL_SUB_LT; REAL_LT_SUB_LADD; REAL_ADD_SYM; REAL_LET_TRANS;
            DIST_TRIANGLE_ALT]);;

let CENTRE_IN_BALL = prove
 (`!x e. x IN ball_fan(x,e) <=> &0 < e`,
  MESON_TAC[IN_BALL_FAN; DIST_REFL]);;

let OPEN_CONTAINS_BALL_FAN = prove
 (`!s. open_fan s <=> !x. x IN s ==> ?e. &0 < e /\ ball_fan(x,e) SUBSET s`,
  REWRITE_TAC[open_def_fan; SUBSET; IN_BALL_FAN] THEN REWRITE_TAC[DIST_SYM]);;

let BALL_EQ_EMPTY_FAN = prove
 (`!x e. (ball_fan(x,e) = {}) <=> e <= &0`,
  REWRITE_TAC[EXTENSION; IN_BALL_FAN; NOT_IN_EMPTY; REAL_NOT_LT] THEN
  MESON_TAC[DIST_POS_LE; REAL_LE_TRANS; DIST_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Basic "localization" results are handy for connectedness.                 *)
(* ------------------------------------------------------------------------- *)

 let OPEN_IN_OPEN_FAN = prove
 (`!s:real^N->bool u. s open_in u <=> ?t. open_fan t /\ (s = u INTER t)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[open_in] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC);
    DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC)) THEN
    REWRITE_TAC[open_def_fan; open_in; SUBSET; IN_INTER] THEN MESON_TAC[]] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `d:real^N->real`) THEN
  EXISTS_TAC `UNIONS {b | ?x:real^N. (b = ball_fan(x,d x)) /\ x IN s}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_UNIONS_FAN THEN
    ASM_SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM; OPEN_BALL_FAN];
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_MESON_TAC[SUBSET; DIST_REFL; DIST_SYM; IN_BALL_FAN]]);;

let CLOSED_IN_CLOSED_FAN = prove
 (`!s:real^N->bool u. s closed_in u <=> ?t. closed_fan t /\ (s = u INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[closed_in; closed_fan; OPEN_IN_OPEN_FAN] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM EXISTS_DIFF] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* These "transitivity" results are handy too.                               *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_TRANS_FAN = prove
 (`!s t u. s open_in t /\ t open_in u ==> s open_in u`,
  ASM_MESON_TAC[OPEN_IN_OPEN_FAN; OPEN_INTER_FAN; INTER_ASSOC]);;

let OPEN_IN_OPEN_TRANS_FAN = prove
 (`!s t. s open_in t /\ open_fan t ==> open_fan s`,
  MESON_TAC[OPEN_IN_FAN; OPEN_IN_TRANS_FAN; OPEN_UNIV_FAN]);;

let CLOSED_IN_TRANS_FAN = prove
 (`!s t u. s closed_in t /\ t closed_in u ==> s closed_in u`,
  ASM_MESON_TAC[CLOSED_IN_CLOSED_FAN; CLOSED_INTER_FAN; INTER_ASSOC]);;

let CLOSED_IN_CLOSED_TRANS_FAN = prove
 (`!s t. s closed_in t /\ closed_fan t ==> closed_fan s`,
  MESON_TAC[CLOSED_IN_FAN; CLOSED_IN_TRANS_FAN; CLOSED_UNIV_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Connectedness.                                                            *)
(* ------------------------------------------------------------------------- *)


let connected_fan = new_definition
  `connected_fan s <=>
      ~(?e1 e2. open_fan e1 /\ open_fan e2 /\ s SUBSET (e1 UNION e2) /\
                (e1 INTER e2 INTER s = {}) /\
                ~(e1 INTER s = {}) /\ ~(e2 INTER s = {}))`;;

(* error in old file*)
let CONNECTED_CLOPEN_FAN = prove
 (`!s. connected_fan s <=>
      !t. t open_in s /\ t closed_in s ==> (t = {}) \/ (t = s)`,
  GEN_TAC THEN REWRITE_TAC[connected_fan; OPEN_IN_OPEN_FAN; CLOSED_IN_CLOSED_FAN] THEN  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o BINDER_CONV) [GSYM EXISTS_DIFF] THEN
  ONCE_REWRITE_TAC[TAUT `(~a <=> b) <=> (a <=> ~b)`] THEN  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; GSYM CONJ_ASSOC; DE_MORGAN_THM] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> b /\ a /\ c /\ d`] THEN  
REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN REWRITE_TAC[GSYM closed] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[TAUT `(a /\ b) /\ (c /\ d) /\ e <=> a /\ c /\ b /\ d /\ e`] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2; closed_fan]
THEN AP_TERM_TAC
THEN AP_TERM_TAC
THEN SET_TAC[]);;


let CONNECTED_EMPTY_FAN = prove
 (`connected_fan {}`,
  REWRITE_TAC[connected_fan; INTER_EMPTY]);;


(* ------------------------------------------------------------------------- *)
(* Limit points.                                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("limit_point_of_fan",(12,"right"));;


let limit_point_of_fan = new_definition
 `x limit_point_of_fan s <=>
        !t. x IN t /\ open_fan t ==> ?y. ~(y = x) /\ y IN s /\ y IN t`;;

let LIMPT_APPROACHABLE_FAN = prove
 (`!x s. x limit_point_of_fan s <=>
                !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ dist(x',x) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[limit_point_of_fan] THEN
  MESON_TAC[open_def_fan; DIST_SYM; OPEN_BALL_FAN; CENTRE_IN_BALL; IN_BALL_FAN]);;

let LIMPT_APPROACHABLE_LE_FAN = prove
 (`!x s. x limit_point_of_fan s <=>
                !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ dist(x',x) <= e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE_FAN] THEN
  MATCH_MP_TAC(TAUT `(~a <=> ~b) ==> (a <=> b)`) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> c ==> ~(a /\ b)`; APPROACHABLE_LT_LE]);;

let LIMPT_UNIV_FAN = prove
 (`!x:real^N. x limit_point_of_fan UNIV`,
  GEN_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE_FAN; IN_UNIV] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?c:real^N. norm(c) = e / &2` CHOOSE_TAC THENL
   [ASM_SIMP_TAC[VECTOR_CHOOSE_SIZE; REAL_HALF; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXISTS_TAC `x + c:real^N` THEN
  REWRITE_TAC[dist; VECTOR_EQ_ADDR] THEN ASM_REWRITE_TAC[VECTOR_ADD_SUB] THEN
  SUBGOAL_THEN `&0 < e / &2 /\ e / &2 < e`
   (fun th -> ASM_MESON_TAC[th; NORM_0; REAL_LT_REFL]) THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

let CLOSED_LIMPT_FAN = prove
 (`!s. closed_fan s <=> !x. x limit_point_of_fan s ==> x IN s`,
  REWRITE_TAC[closed_fan] THEN ONCE_REWRITE_TAC[OPEN_SUBOPEN_FAN] THEN
  REWRITE_TAC[limit_point_of_fan; IN_DIFF; IN_UNIV; SUBSET] THEN MESON_TAC[]);;

let LIMPT_SUBSET_FAN = prove
 (`!x s t. x limit_point_of_fan s /\ s SUBSET t ==> x limit_point_of_fan t`,
  REWRITE_TAC[limit_point_of_fan; SUBSET] THEN MESON_TAC[]);;

let LIMPT_EMPTY_FAN = prove
 (`!x. ~(x limit_point_of_fan {})`,
  REWRITE_TAC[LIMPT_APPROACHABLE_FAN; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LT_01]);;

let CLOSED_POSITIVE_ORTHANT_FAN = prove
 (`closed_fan {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                          ==> &0 <= x$i}`,
  REWRITE_TAC[CLOSED_LIMPT_FAN; LIMPT_APPROACHABLE_FAN] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `--(x:real^N $ i)`) THEN
  ASM_REWRITE_TAC[REAL_LT_RNEG; REAL_ADD_LID; NOT_EXISTS_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  MATCH_MP_TAC(TAUT `(a ==> ~c) ==> ~(a /\ b /\ c)`) THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!b. abs x <= b /\ b <= a ==> ~(a + x < &0)`) THEN
  EXISTS_TAC `abs((y - x :real^N)$i)` THEN
  ASM_SIMP_TAC[dist; COMPONENT_LE_NORM] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; REAL_ARITH
   `x < &0 /\ &0 <= y ==> abs(x) <= abs(y - x)`]);;

(* ------------------------------------------------------------------------- *)
(* Interior of a set.                                                        *)
(* ------------------------------------------------------------------------- *)

let interior_fan = new_definition
  `interior_fan s = {x | ?t. open_fan t /\ x IN t /\ t SUBSET s}`;;

let INTERIOR_EQ_FAN = prove
 (`!s. (interior_fan s = s) <=> open_fan s`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; interior_fan; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [OPEN_SUBOPEN_FAN] THEN MESON_TAC[SUBSET]);;

let INTERIOR_OPEN_FAN = prove
 (`!s. open_fan s ==> (interior_fan s = s)`,
  MESON_TAC[INTERIOR_EQ_FAN]);;

let OPEN_INTERIOR_FAN = prove
 (`!s. open_fan(interior_fan s)`,
  GEN_TAC THEN REWRITE_TAC[interior_fan] THEN GEN_REWRITE_TAC I [OPEN_SUBOPEN_FAN] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERIOR_INTERIOR_FAN = prove
 (`!s. interior_fan(interior_fan s) = interior_fan s`,
  MESON_TAC[INTERIOR_EQ_FAN; OPEN_INTERIOR_FAN]);;

let INTERIOR_SUBSET_FAN = prove
 (`!s. (interior_fan s) SUBSET s`,
  REWRITE_TAC[SUBSET; interior_fan; IN_ELIM_THM] THEN MESON_TAC[]);;

let SUBSET_INTERIOR_FAN = prove
 (`!s t. s SUBSET t ==> (interior_fan s) SUBSET (interior_fan t)`,
  REWRITE_TAC[interior_fan; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERIOR_MAXIMAL_FAN = prove
 (`!s t. t SUBSET s /\ open_fan t ==> t SUBSET (interior_fan s)`,
  REWRITE_TAC[interior_fan; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERIOR_UNIQUE_FAN = prove
 (`!s t. t SUBSET s /\ open_fan t /\ (!t'. t' SUBSET s /\ open_fan t' ==> t' SUBSET t)
         ==> (interior_fan s = t)`,
  MESON_TAC[SUBSET_ANTISYM; INTERIOR_MAXIMAL_FAN; INTERIOR_SUBSET_FAN;
            OPEN_INTERIOR_FAN]);;

let IN_INTERIOR_FAN = prove
 (`!x s. x IN interior_fan s <=> ?e. &0 < e /\ ball_fan(x,e) SUBSET s`,
  REWRITE_TAC[interior_fan; IN_ELIM_THM] THEN
  MESON_TAC[OPEN_CONTAINS_BALL_FAN; SUBSET_TRANS; CENTRE_IN_BALL; OPEN_BALL_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Closure of a set.                                                         *)
(* ------------------------------------------------------------------------- *)

let closure_fan = new_definition
  `closure_fan s = s UNION {x | x limit_point_of_fan s}`;;

let CLOSURE_INTERIOR_FAN = prove
 (`!s:real^N->bool. closure_fan s = UNIV DIFF (interior_fan (UNIV DIFF s))`,
  REWRITE_TAC[EXTENSION; closure_fan; IN_UNION; IN_DIFF; IN_UNIV; interior_fan;
              IN_ELIM_THM; limit_point_of_fan; SUBSET] THEN
  MESON_TAC[]);;

let lemma_interior_closure = prove(`!s t. UNIV DIFF (UNIV DIFF t) = t`,SET_TAC[]);;

let INTERIOR_CLOSURE_FAN = prove
 (`!s:real^N->bool. interior_fan s = UNIV DIFF (closure_fan (UNIV DIFF s))`,
    REWRITE_TAC[CLOSURE_INTERIOR_FAN; lemma_interior_closure]);;

  let lemma_closed_closure = prove(`UNIV DIFF (UNIV DIFF s) = s`,SET_TAC[]);;

let CLOSED_CLOSURE_FAN = prove
 (`!s. closed_fan(closure_fan s)`,
   REWRITE_TAC[closed_fan; CLOSURE_INTERIOR_FAN; lemma_closed_closure; OPEN_INTERIOR_FAN]);;

let CLOSURE_HULL_FAN = prove
 (`!s. closure_fan s = closed_fan hull s`,
  GEN_TAC THEN MATCH_MP_TAC(GSYM HULL_UNIQUE) THEN
  REWRITE_TAC[CLOSED_CLOSURE_FAN; SUBSET] THEN
  REWRITE_TAC[closure_fan; IN_UNION; IN_ELIM_THM; CLOSED_LIMPT_FAN] THEN
  MESON_TAC[limit_point_of_fan]);;

let CLOSURE_EQ_FAN = prove
 (`(closure_fan s = s) <=> closed_fan s`,
  SIMP_TAC[CLOSURE_HULL_FAN; HULL_EQ; CLOSED_INTERS_FAN]);;

let CLOSURE_CLOSED_FAN = prove
 (`!s. closed_fan s ==> (closure_fan s = s)`,
  MESON_TAC[CLOSURE_EQ_FAN]);;

let CLOSURE_CLOSURE_FAN = prove
 (`!s. closure_fan (closure_fan s) = closure_fan s`,
  REWRITE_TAC[CLOSURE_HULL_FAN; HULL_HULL]);;

let CLOSURE_SUBSET_FAN = prove
 (`!s. s SUBSET (closure_fan s)`,
  REWRITE_TAC[CLOSURE_HULL_FAN; HULL_SUBSET]);;

let SUBSET_CLOSURE_FAN = prove
 (`!s t. s SUBSET t ==> (closure_fan s) SUBSET (closure_fan t)`,
  REWRITE_TAC[CLOSURE_HULL_FAN; HULL_MONO]);;

let CLOSURE_MINIMAL_FAN = prove
 (`!s t. s SUBSET t /\ closed_fan t ==> (closure_fan s) SUBSET t`,
  REWRITE_TAC[HULL_MINIMAL; CLOSURE_HULL_FAN]);;

let CLOSURE_UNIQUE_FAN = prove
 (`!s t. s SUBSET t /\ closed_fan t /\
         (!t'. s SUBSET t' /\ closed_fan t' ==> t SUBSET t')
         ==> (closure_fan s = t)`,
  REWRITE_TAC[CLOSURE_HULL_FAN; HULL_UNIQUE]);;

(* ------------------------------------------------------------------------- *)
(* Frontier (aka boundary).                                                  *)
(* ------------------------------------------------------------------------- *)

let frontier_fan = new_definition
  `frontier_fan s = (closure_fan s) DIFF (interior_fan s)`;;

let FRONTIER_CLOSED_FAN = prove
 (`!s. closed_fan(frontier_fan s)`,
  SIMP_TAC[frontier_fan; CLOSED_DIFF_FAN; CLOSED_CLOSURE_FAN; OPEN_INTERIOR_FAN]);;

  let frotier_closures_fan = prove(`s DIFF (UNIV DIFF t) = s INTER t`,SET_TAC[]);;

let FRONTIER_CLOSURES_FAN = prove
 (`!s:real^N->bool. frontier_fan s = (closure_fan s) INTER (closure_fan(UNIV DIFF s))`,
  REWRITE_TAC[frontier_fan; INTERIOR_CLOSURE_FAN; frotier_closures_fan]);;


let FRONTIER_STRADDLE_FAN = prove
 (`!a:real^N s.
     a IN frontier_fan s <=>
        !e. &0 < e ==> (?x. x IN s /\ dist(a,x) < e) /\
                       (?x. ~(x IN s) /\ dist(a,x) < e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRONTIER_CLOSURES_FAN; IN_INTER] THEN
  REWRITE_TAC[closure_fan; IN_UNION; IN_ELIM_THM; limit_point_of_fan;
              IN_UNIV; IN_DIFF] THEN
  ASM_MESON_TAC[IN_BALL_FAN; SUBSET; OPEN_CONTAINS_BALL_FAN;
                CENTRE_IN_BALL; OPEN_BALL_FAN; DIST_REFL]);;

let FRONTIER_SUBSET_CLOSED_FAN = prove
 (`!s. closed_fan s ==> (frontier_fan s) SUBSET s`,
  MESON_TAC[frontier_fan; CLOSURE_CLOSED_FAN; SUBSET_DIFF]);;





(* ------------------------------------------------------------------------- *)
(* A variant of nets (slightly non-standard but good for our purposes).      *)
(* ------------------------------------------------------------------------- *)

let net_tybij_fan = new_type_definition "net_fan" ("mk_net_fan","netord_fan")
 (prove
   (`?g:A->A->bool. !x y. (!z. g z x ==> g z y) \/ (!z. g z y ==> g z x)`,
    EXISTS_TAC `\x:A y:A. F` THEN REWRITE_TAC[]));;

let NET_FAN = prove
 (`!n x y. (!z. netord_fan n z x ==> netord_fan n z y) \/
           (!z. netord_fan n z y ==> netord_fan n z x)`,
   REWRITE_TAC[net_tybij_fan; ETA_AX]);;

let OLDNET_FAN = prove
 (`!n x y. netord_fan n x x /\ netord_fan n y y
           ==> ?z. netord_fan n z z /\
                   !w. netord_fan n w z ==> netord_fan n w x /\ netord_fan n w y`,
  MESON_TAC[NET_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Common nets and the "within" modifier for nets.                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("within_fan",(14,"right"));;
parse_as_infix("in_direction_fan",(14,"right"));;

let at_fan = new_definition
  `at_fan a = mk_net_fan(\x y. &0 < dist(x,a) /\ dist(x,a) <= dist(y,a))`;;

let at_infinity_fan = new_definition
  `at_infinity_fan = mk_net_fan(\x y. norm(x) >= norm(y))`;;

let sequentially_fan = new_definition
  `sequentially_fan = mk_net_fan(\m:num n. m >= n)`;;

let within_fan = new_definition
  `net_fan within_fan s = mk_net_fan(\x y. netord_fan net_fan x y /\ x IN s)`;;

let in_direction_fan = new_definition
  `a in_direction_fan v = (at_fan a) within_fan {b | ?c. &0 <= c /\ (b - a = c % v)}`;;

(* ------------------------------------------------------------------------- *)
(* Prove that they are all nets.                                             *)
(* ------------------------------------------------------------------------- *)

let NET_PROVE_FAN_TAC[def] =
  REWRITE_TAC[GSYM FUN_EQ_THM; def] THEN
  REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[GSYM(CONJUNCT2 net_tybij_fan)];;

let AT_FAN = prove
 (`!a:real^N x y.
        netord_fan(at_fan a) x y <=> &0 < dist(x,a) /\ dist(x,a) <= dist(y,a)`,
  GEN_TAC THEN NET_PROVE_FAN_TAC[at_fan] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS; REAL_LET_TRANS]);;

let AT_INFINITY_FAN = prove
 (`!a:real^N x y. netord_fan at_infinity_fan x y <=> norm(x) >= norm(y)`,
  GEN_TAC THEN NET_PROVE_FAN_TAC[at_infinity_fan] THEN
  REWRITE_TAC[real_ge; REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_REFL; REAL_LE_TRANS]);;

let SEQUENTIALLY_FAN = prove
 (`!m n. netord_fan sequentially_fan m n <=> m >= n`,
  NET_PROVE_FAN_TAC[sequentially_fan] THEN REWRITE_TAC[GE; LE_REFL] THEN
  MESON_TAC[LE_CASES; LE_REFL; LE_TRANS]);;

let WITHIN_FAN = prove
 (`!n s x y. netord_fan(n within_fan s) x y <=> netord_fan n x y /\ x IN s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[within_fan; GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 net_tybij_fan); ETA_AX] THEN
  MESON_TAC[NET_FAN]);;

let IN_DIRECTION_FAN = prove
 (`!a v x y. netord_fan(a in_direction_fan v) x y <=>
                &0 < dist(x,a) /\ dist(x,a) <= dist(y,a) /\
                 ?c. &0 <= c /\ (x - a = c % v)`,
  REWRITE_TAC[WITHIN_FAN; AT_FAN; in_direction_fan; IN_ELIM_THM; CONJ_ACI]);;

let WITHIN_UNIV_FAN = prove
 (`!x:real^N. at_fan x within_fan UNIV = at_fan x`,
  REWRITE_TAC[within_fan; at_fan; IN_UNIV] THEN REWRITE_TAC[ETA_AX; net_tybij_fan]);;

(* ------------------------------------------------------------------------- *)
(* Identify trivial limits, where we can't approach arbitrarily closely.     *)
(* ------------------------------------------------------------------------- *)

let trivial_limit_fan = new_definition
  `trivial_limit_fan net_fan <=>
     (!a:A b. a = b) \/
     ?a:A b. ~(a = b) /\ !x. ~(netord_fan(net_fan) x a) /\ ~(netord_fan(net_fan) x b)`;;

let TRIVIAL_LIMIT_WITHIN_FAN = prove
 (`!a:real^N. trivial_limit_fan (at_fan a within_fan s) <=> ~(a limit_point_of_fan s)`,
  REWRITE_TAC[trivial_limit_fan; LIMPT_APPROACHABLE_LE_FAN; WITHIN_FAN; AT_FAN; DIST_NZ] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [MESON_TAC[REAL_LT_01; REAL_LT_REFL; VECTOR_CHOOSE_DIST;
                DIST_REFL; REAL_LT_IMP_LE];
      DISCH_THEN(X_CHOOSE_THEN `b:real^N` (X_CHOOSE_THEN `c:real^N`
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `&0 < dist(a,b:real^N) \/ &0 < dist(a,c:real^N)` MP_TAC THEN
      ASM_MESON_TAC[DIST_TRIANGLE; DIST_SYM; GSYM DIST_NZ; GSYM DIST_EQ_0;
                    REAL_ARITH `x <= &0 + &0 ==> ~(&0 < x)`]];
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN DISJ2_TAC THEN
    EXISTS_TAC `a:real^N` THEN
    SUBGOAL_THEN `?b:real^N. dist(a,b) = e` MP_TAC THENL
     [ASM_SIMP_TAC[VECTOR_CHOOSE_DIST; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^N` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_MESON_TAC[REAL_NOT_LE; DIST_REFL; DIST_NZ; DIST_SYM]]);;


let TRIVIAL_LIMIT_AT_FAN = prove
 (`!a. ~(trivial_limit_fan (at_fan a))`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV_FAN] THEN
  REWRITE_TAC[TRIVIAL_LIMIT_WITHIN_FAN; LIMPT_UNIV_FAN]);;

let TRIVIAL_LIMIT_AT_INFINITY_FAN = prove
 (`~(trivial_limit_fan at_infinity_fan)`,
  REWRITE_TAC[trivial_limit_fan; AT_INFINITY_FAN; real_ge] THEN
  MESON_TAC[REAL_LE_REFL; VECTOR_CHOOSE_SIZE; REAL_LT_01; REAL_LT_LE]);;

let TRIVIAL_LIMIT_SEQUENTIALLY_FAN = prove
 (`~(trivial_limit_fan sequentially_fan)`,
  REWRITE_TAC[trivial_limit_fan; SEQUENTIALLY_FAN] THEN
  MESON_TAC[GE_REFL; NOT_SUC]);;

(* ------------------------------------------------------------------------- *)
(* Limits, defined as vacuously true when the limit is trivial.              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("-->",(12,"right"));;

let lim_fan = new_definition
  `(f --> l) net_fan <=>
        trivial_limit_fan net_fan \/
        !e. &0 < e ==> ?y. (?x.  netord_fan(net_fan) x y) /\
                           !x. netord_fan(net_fan) x y ==> dist(f(x),l) < e`;;

(* ------------------------------------------------------------------------- *)
(* Show that they yield usual definitions in the various cases.              *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_LE_FAN = prove
 (`!f:real^M->real^N l a s.
        (f --> l)(at_fan a within_fan s) <=>
           !e. &0 < e ==> ?d. &0 < d /\
                              !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) <= d
                                   ==> dist(f(x),l) < e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[lim_fan; AT_FAN; WITHIN_FAN; TRIVIAL_LIMIT_WITHIN_FAN] THEN
  REWRITE_TAC[LIMPT_APPROACHABLE_LE_FAN; DIST_NZ] THEN EQ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [ALL_TAC; MATCH_MP_TAC MONO_FORALL] THEN MESON_TAC[REAL_LTE_TRANS];
    MATCH_MP_TAC(TAUT `(b ==> a ==> c) ==> (a ==> ~b \/ c)`) THEN
    DISCH_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC `e:real` THEN ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?b:real^M. dist(a,b) = d` MP_TAC THENL
     [ASM_SIMP_TAC[VECTOR_CHOOSE_DIST; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:real^M` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_MESON_TAC[REAL_NOT_LE; DIST_REFL; DIST_NZ; DIST_SYM]]);;

let LIM_WITHIN_FAN = prove
 (`!f:real^M->real^N l a s.
      (f --> l) (at_fan a within_fan s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x. x IN s /\ &0 < dist(x,a) /\ dist(x,a) < d
                    ==> dist(f(x),l) < e`,
  REWRITE_TAC[LIM_WITHIN_LE_FAN] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`] THEN
  REWRITE_TAC[APPROACHABLE_LT_LE]);;

let LIM_AT_FAN = prove
 (`!f l:real^N a:real^M.
      (f --> l) (at_fan a) <=>
              !e. &0 < e
                  ==> ?d. &0 < d /\ !x. &0 < dist(x,a) /\ dist(x,a) < d
                          ==> dist(f(x),l) < e`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV_FAN] THEN
  REWRITE_TAC[LIM_WITHIN_FAN; IN_UNIV]);;

let LIM_AT_INFINITY_FAN = prove
 (`!f l. (f --> l) at_infinity_fan <=>
               !e. &0 < e ==> ?b. !x. norm(x) >= b ==> dist(f(x),l) < e`,
  REWRITE_TAC[lim_fan; AT_INFINITY_FAN; TRIVIAL_LIMIT_AT_INFINITY_FAN] THEN
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN
  MESON_TAC[real_ge; REAL_LE_REFL; VECTOR_CHOOSE_SIZE;
    REAL_ARITH `&0 <= b \/ (!x. x >= &0 ==> x >= b)`]);;

let LIM_SEQUENTIALLY_FAN = prove
 (`!s l. (s --> l) sequentially_fan <=>
          !e. &0 < e ==> ?N. !n. N <= n ==> dist(s(n),l) < e`,
  REWRITE_TAC[lim_fan; SEQUENTIALLY_FAN; GE; LE_REFL; TRIVIAL_LIMIT_SEQUENTIALLY_FAN] THEN
  MESON_TAC[LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The expected monotonicity property.                                       *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_SUBSET_FAN = prove
 (`!f l a s.
    (f --> l) (at_fan a within_fan s) /\ t SUBSET s ==> (f --> l) (at_fan a within_fan t)`,
  REWRITE_TAC[LIM_WITHIN_FAN; SUBSET] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Interrelations between restricted and unrestricted limits.                *)
(* ------------------------------------------------------------------------- *)

let LIM_AT_WITHIN_FAN = prove
 (`!f l a s. (f --> l)(at_fan a) ==> (f --> l)(at_fan a within_fan s)`,
  REWRITE_TAC[LIM_AT_FAN; LIM_WITHIN_FAN] THEN MESON_TAC[]);;

let LIM_WITHIN_OPEN_FAN = prove
 (`!f l a:real^M s.
     a IN s /\ open_fan s ==> ((f --> l)(at_fan a within_fan s) <=> (f --> l)(at_fan a))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[LIM_AT_WITHIN_FAN] THEN
  REWRITE_TAC[LIM_AT_FAN; LIM_WITHIN_FAN] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:real^M` o GEN_REWRITE_RULE I [open_def_fan]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REAL_LT_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Another limit point characterization.                                     *)
(* ------------------------------------------------------------------------- *)

let LIMPT_SEQUENTIAL_FAN = prove
 (`!x:real^N s.
      x limit_point_of_fan s <=>
             ?f. (!n. f(n) IN (s DELETE x)) /\ (f --> x) sequentially_fan`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIMPT_APPROACHABLE_FAN; LIM_SEQUENTIALLY_FAN; IN_DELETE] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[GE; LE_REFL]] THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 <= x ==> &0 < x + &1`; REAL_POS] THEN
  REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `f:num->real^N` THEN REWRITE_TAC[FORALL_AND_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FORALL_POS_MONO_1 THEN
  CONJ_TAC THENL [MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN EXISTS_TAC `n:num` THEN REWRITE_TAC[GSYM GE] THEN
  MATCH_MP_TAC SEQ_MONO_LEMMA THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[REAL_LE_INV2; GE; REAL_OF_NUM_LE; REAL_LE_RADD; GE_REFL;
           REAL_POS; REAL_ARITH `&0 <= x ==> &0 < x + &1`]);;


(* ------------------------------------------------------------------------- *)
(* Basic arithmetical combining theorems for limits.                         *)
(* ------------------------------------------------------------------------- *)

let NET_DILEMMA_FAN = prove
 (`!net. (?a. (?x. netord_fan net_fan x a) /\ (!x. netord_fan net_fan x a ==> P x)) /\
         (?b. (?x. netord_fan net_fan x b) /\ (!x. netord_fan net_fan x b ==> Q x))
         ==> ?c. (?x. netord_fan net_fan x c) /\ (!x. netord_fan net_fan x c ==> P x /\ Q x)`,
  MESON_TAC[NET_FAN]);;

let LIM_LINEAR_FAN = prove
 (`!net_fan:(A)net_fan h f l.
        (f --> l) net_fan /\ linear h ==> ((\x. h(f x)) --> h l) net_fan`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lim_fan] THEN
  ASM_CASES_TAC `trivial_limit_fan (net_fan:(A)net_fan)` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o
    MATCH_MP LINEAR_BOUNDED_POS) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / B`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; dist; GSYM LINEAR_SUB; REAL_LT_RDIV_EQ] THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_MUL_SYM]);;

let LIM_CONST_FAN = prove
 (`!net_fan a:real^N. ((\x. a) --> a) net_fan`,
  SIMP_TAC[lim_fan; DIST_REFL; trivial_limit_fan] THEN MESON_TAC[]);;

let LIM_CMUL_FAN = prove
 (`!f l c. (f --> l) net_fan ==> ((\x. c % f x) --> c % l) net_fan`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_LINEAR_FAN THEN
  ASM_REWRITE_TAC[REWRITE_RULE[ETA_AX]
    (MATCH_MP LINEAR_COMPOSE_CMUL LINEAR_ID)]);;

let LIM_NEG_FAN = prove
 (`!f l:real^N. (f --> l) net_fan ==> ((\x. --(f x)) --> --l) net_fan`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lim_fan; dist] THEN
  REWRITE_TAC[VECTOR_ARITH `--x - --y = --(x - y:real^N)`; NORM_NEG]);;
(* error in old file*)

let LIM_ADD_FAN = prove
 (`!net_fan:(A)net_fan f g l m.
    (f --> l) net_fan /\ (g --> m) net_fan ==> ((\x. f(x) + g(x)) --> l + m) net_fan`,
 REPEAT GEN_TAC THEN REWRITE_TAC[lim_fan] THEN
  ASM_CASES_TAC `trivial_limit_fan (net_fan:(A)net_fan)` THEN
  ASM_REWRITE_TAC[AND_FORALL_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NET_DILEMMA_FAN) THEN REWRITE_TAC[MONO_EXISTS] THEN
 MESON_TAC[REAL_HALF; DIST_TRIANGLE_ADD; REAL_LT_ADD2; REAL_LET_TRANS]);;


let LIM_SUB_FAN = prove
 (`!net_fan:(A)net_fan f g l m.
    (f --> l) net_fan /\ (g --> m) net_fan ==> ((\x. f(x) - g(x)) --> l - m) net_fan`,
  REWRITE_TAC[real_sub; VECTOR_SUB] THEN ASM_SIMP_TAC[LIM_ADD_FAN; LIM_NEG_FAN]);;

let LIM_NULL_FAN = prove
 (`!net_fan f l. (f --> l) net_fan <=> ((\x. f(x) - l) --> vec 0) net_fan`,
  REWRITE_TAC[lim_fan; dist; VECTOR_SUB_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* We need some non-triviality conditions on these two.                      *)
(* ------------------------------------------------------------------------- *)

let LIM_NORM_BOUND_FAN = prove
 (`!f (l:real^N) net_fan:(A)net_fan.
      ~(trivial_limit_fan net_fan) /\ (f --> l) net_fan /\
      (?y. (?x. netord_fan net_fan x y) /\ !x. netord_fan net_fan x y ==> norm(f x) <= e)
      ==> norm(l) <= e`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[lim_fan] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?x:A. dist(f(x):real^N,l) < norm(l:real^N) - e /\ norm(f x) <= e`
  (CHOOSE_THEN MP_TAC) THENL [ASM_MESON_TAC[NET_FAN]; ALL_TAC] THEN
  REWRITE_TAC[REAL_NOT_LT; REAL_LE_SUB_RADD; DE_MORGAN_THM; dist] THEN
  ASM_MESON_TAC[NORM_TRIANGLE; NORM_SUB; VECTOR_SUB_ADD;
    REAL_ARITH `nl <= nd + nx /\ nx <= e ==> nl <= nd + e`]);;

let LIM_UNIQUE_FAN = prove
 (`!net_fan:(A)net_fan f l:real^N l'.
      ~(trivial_limit_fan net_fan) /\ (f --> l) net_fan /\ (f --> l') net_fan ==> (l = l')`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[VECTOR_SUB_REFL] o MATCH_MP LIM_SUB_FAN) THEN
  SUBGOAL_THEN `!e. &0 < e ==> norm(l:real^N - l') <= e` MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC LIM_NORM_BOUND_FAN THEN
    MAP_EVERY EXISTS_TAC [`\x:A. vec 0 : real^N`; `net_fan:(A)net_fan`] THEN
    ASM_SIMP_TAC[NORM_0; REAL_LT_IMP_LE] THEN ASM_MESON_TAC[trivial_limit_fan];
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[DIST_NZ; dist] THEN
    DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `norm(l - l':real^N) / &2`) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    UNDISCH_TAC `&0 < norm(l - l':real^N)` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Limit under bilinear function (surprisingly tedious, but important).      *)
(* ------------------------------------------------------------------------- *)

let NORM_BOUND_LEMMA_FAN = prove
 (`!x:real^M y:real^N e.
        &0 < e
        ==> ?d. &0 < d /\
                !x' y'. norm(x' - x) < d /\ norm(y' - y) < d
                        ==> norm(x') * norm(y' - y) + norm(x' - x) * norm(y)
                                < e`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `min (&1) (e / &2 / (norm(x:real^M) + norm(y:real^N) + &1))` THEN
  ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_OF_NUM_LT; NORM_POS_LE; ARITH;
    REAL_LT_RDIV_EQ; REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 < x + y + &1`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
   `(norm(x:real^M) + &1) * norm(y' - y) + norm(x' - x) * norm(y:real^N)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_RADD; GSYM REAL_ADD_RDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_MESON_TAC[NORM_TRIANGLE_SUB; REAL_ARITH
     `x' <= x + d /\ d < &1 ==> x' <= x + &1`];
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(norm(x:real^M) + norm(y:real^N) + &1) *
                (norm(x' - x) + norm(y' - y))` THEN
    CONJ_TAC THENL [ALL_TAC; REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `y * xd <= p * xd /\ x * yd <= p * yd
      ==> x * yd + xd * y <= p * (xd + yd)`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THENL
     [MP_TAC(ISPEC `x:real^M` NORM_POS_LE);
      MP_TAC(ISPEC `y:real^N` NORM_POS_LE)] THEN
    REAL_ARITH_TAC]);;

(*let LIM_BILINEAR_FAN = prove
 (;;
g`!net_fan:(A)net_fan (h:real^M->real^N->real^P) f g l m.
        (f --> l) net_fan /\ (g --> m) net_fan /\ bilinear h
        ==> ((\x. h (f x) (g x)) --> (h l m)) net_fan`;;
,;;
 e( REPEAT GEN_TAC THEN REWRITE_TAC[lim_fan] THEN
  ASM_CASES_TAC `trivial_limit_fan (net_fan:(A)net_fan)` THEN
  ASM_REWRITE_TAC[AND_FORALL_THM; CONJ_ASSOC] THEN
  STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o  MATCH_MP
   BILINEAR_BOUNDED_POS) THEN
  MP_TAC(ISPECL [`l:real^M`; `m:real^N`; `e / B`] NORM_BOUND_LEMMA_FAN) THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NET_DILEMMA_FAN));;
  THEN 
;;
e(REWRITE_TAC[MONO_EXISTS]);;

THEN;;

e(X_GEN_TAC `c:A`);;
MONO_AND;; 
e(DISCH_TAC);;

e( MATCH_MP_TAC MONO_AND);; 

THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `a:A` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[dist] THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th)) THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH
    `h a b - h c d :real^N = (h a b - h a d) + (h a d - h c d)`] THEN
  MATCH_MP_TAC NORM_TRIANGLE_LT THEN
  ASM_SIMP_TAC[GSYM BILINEAR_LSUB; GSYM BILINEAR_RSUB] THEN
  FIRST_X_ASSUM(fun th ->
   MP_TAC(SPECL [`(f:A->real^M) a`; `(g:A->real^N) a - m`] th) THEN
   MP_TAC(SPECL [`(f:A->real^M) a - l`; `m:real^N`] th)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;
*)

(* ------------------------------------------------------------------------- *)
(* These are special for limits out of the same vector space.                *)
(* ------------------------------------------------------------------------- *)

let LIM_WITHIN_ID_FAN = prove
 (`!a s. ((\x. x) --> a) (at_fan a within_fan s)`,
  REWRITE_TAC[LIM_WITHIN_FAN] THEN MESON_TAC[]);;

let LIM_AT_ID_FAN = prove
 (`!a. ((\x. x) --> a) (at_fan a)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV_FAN] THEN REWRITE_TAC[LIM_WITHIN_ID_FAN]);;
  
let LIM_AT_ZERO_FAN = prove
 (`!f:real^M->real^N l a.
        (f --> l) (at_fan a) <=> ((\x. f(a + x)) --> l) (at_fan(vec 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_AT_FAN] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  ASM_CASES_TAC `&0 < d` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:real^M` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a + x:real^M`) THEN
    REWRITE_TAC[dist; VECTOR_ADD_SUB; VECTOR_SUB_RZERO];
    FIRST_X_ASSUM(MP_TAC o SPEC `x - a:real^M`) THEN
    REWRITE_TAC[dist; VECTOR_SUB_RZERO; VECTOR_SUB_ADD2]]);;

(* ------------------------------------------------------------------------- *)
(* It's also sometimes useful to extract the limit point from the net.       *)
(* ------------------------------------------------------------------------- *)

let netlimit_fan = new_definition
  `netlimit_fan net_fan = @a. !x. ~(netord_fan net_fan x a)`;;

let NETLIMIT_WITHIN_FAN = prove
 (`!a:real^N s. ~(trivial_limit_fan (at_fan a within_fan s))
                ==> (netlimit_fan (at_fan a within_fan s) = a)`,
  REWRITE_TAC[trivial_limit_fan; netlimit_fan; AT_FAN; WITHIN_FAN; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x:real^N. ~(&0 < dist(x,a) /\ dist(x,a) <= dist(a,a) /\ x IN s)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[DIST_REFL; REAL_NOT_LT]; ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Useful lemmas on closure and set of possible sequential limits.           *)
(* ------------------------------------------------------------------------- *)

let CLOSURE_SEQUENTIAL_FAN = prove
 (`!s l:real^N.
     l IN closure_fan(s) <=> ?x. (!n. x(n) IN s) /\ (x --> l) sequentially_fan`,
  REWRITE_TAC[closure_fan; IN_UNION; LIMPT_SEQUENTIAL_FAN; IN_ELIM_THM; IN_DELETE] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT
    `((b ==> c) /\ (~a /\ c ==> b)) /\ (a ==> c) ==> (a \/ b <=> c)`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  EXISTS_TAC `\n:num. l:real^N` THEN
  ASM_REWRITE_TAC[LIM_CONST_FAN]);;

let CLOSED_SEQUENTIAL_LIMITS_FAN = prove
 (`!s. closed_fan s <=>
       !x l. (!n. x(n) IN s) /\ (x --> l) sequentially_fan ==> l IN s`,
  MESON_TAC[CLOSURE_SEQUENTIAL_FAN; CLOSURE_CLOSED_FAN;
            CLOSED_LIMPT_FAN; LIMPT_SEQUENTIAL_FAN; IN_DELETE]);;

let CLOSURE_APPROACHABLE_FAN = prove
 (`!x s. x IN closure_fan(s) <=> !e. &0 < e ==> ?y. y IN s /\ dist(y,x) < e`,
  REWRITE_TAC[closure_fan; LIMPT_APPROACHABLE_FAN; IN_UNION; IN_ELIM_THM] THEN
  MESON_TAC[DIST_REFL]);;

let CLOSED_APPROACHABLE_FAN = prove
 (`!x s. closed_fan s
         ==> ((!e. &0 < e ==> ?y. y IN s /\ dist(y,x) < e) <=> x IN s)`,
  MESON_TAC[CLOSURE_CLOSED_FAN; CLOSURE_APPROACHABLE_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Closed balls.                                                             *)
(* ------------------------------------------------------------------------- *)

let cball_fan = new_definition
  `cball_fan(x,e) = { y | dist(x,y) <= e}`;;

let IN_CBALL_FAN = prove
 (`!x y e. y IN cball_fan(x,e) <=> dist(x,y) <= e`,
  REWRITE_TAC[cball_fan; IN_ELIM_THM]);;

let CLOSED_CBALL_FAN = prove
 (`!x:real^N e. closed_fan(cball_fan(x,e))`,
  REWRITE_TAC[CLOSED_SEQUENTIAL_LIMITS_FAN; IN_CBALL_FAN; dist] THEN
  GEN_TAC THEN GEN_TAC THEN X_GEN_TAC `s:num->real^N` THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `\n. x - (s:num->real^N) n` LIM_NORM_BOUND_FAN) THEN
  EXISTS_TAC `sequentially_fan` THEN REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY_FAN] THEN
  ASM_SIMP_TAC[LIM_SUB_FAN; LIM_CONST_FAN; SEQUENTIALLY_FAN] THEN MESON_TAC[GE_REFL]);;

let CENTRE_IN_CBALL_FAN = prove
 (`!x e. x IN cball_fan(x,e) <=> &0 <= e`,
  MESON_TAC[IN_CBALL_FAN; DIST_REFL]);;

let BALL_SUBSET_CBALL_FAN = prove
 (`!x e. ball_fan(x,e) SUBSET cball_fan(x,e)`,
  REWRITE_TAC[IN_BALL_FAN; IN_CBALL_FAN; SUBSET] THEN REAL_ARITH_TAC);;

let OPEN_CONTAINS_CBALL_FAN = prove
 (`!s. open_fan s <=> !x. x IN s ==> ?e. &0 < e /\ cball_fan(x,e) SUBSET s`,
  GEN_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL_FAN] THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SUBSET_TRANS; BALL_SUBSET_CBALL_FAN]] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[SUBSET; IN_BALL_FAN; IN_CBALL_FAN] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  SUBGOAL_THEN `e / &2 < e` (fun th -> ASM_MESON_TAC[th; REAL_LET_TRANS]) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

let IN_INTERIOR_CBALL_FAN = prove
 (`!x s. x IN interior_fan s <=> ?e. &0 < e /\ cball_fan(x,e) SUBSET s`,
  REWRITE_TAC[interior_fan; IN_ELIM_THM] THEN
  MESON_TAC[OPEN_CONTAINS_CBALL_FAN; SUBSET_TRANS;
            BALL_SUBSET_CBALL_FAN; CENTRE_IN_BALL; OPEN_BALL_FAN]);;

let LIMPT_BALL_FAN = prove
 (`!x:real^N y e. y limit_point_of_fan ball_fan(x,e) <=> &0 < e /\ y IN cball_fan(x,e)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 < e` THENL
   [ALL_TAC; ASM_MESON_TAC[LIMPT_EMPTY_FAN; REAL_NOT_LT; BALL_EQ_EMPTY_FAN]] THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [MESON_TAC[CLOSED_CBALL_FAN; CLOSED_LIMPT_FAN; LIMPT_SUBSET_FAN; BALL_SUBSET_CBALL_FAN];
    REWRITE_TAC[IN_CBALL_FAN; LIMPT_APPROACHABLE_FAN; IN_BALL_FAN]] THEN
  DISCH_TAC THEN X_GEN_TAC `d:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `y:real^N = x` THEN ASM_REWRITE_TAC[DIST_NZ] THENL
   [MP_TAC(SPECL [`d:real`; `e:real`] REAL_DOWN2) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_MESON_TAC 0 40 1 [VECTOR_CHOOSE_DIST; DIST_SYM; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`norm(y:real^N - x)`; `d:real`] REAL_DOWN2) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIST_NZ; dist]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(y:real^N) - (k / dist(y,x)) % (y - x)` THEN
  REWRITE_TAC[dist; VECTOR_ARITH `(y - c % z) - y = --c % z`] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM; REAL_ABS_NEG] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_ARITH `x - (y - k % (y - x)) = (&1 - k) % (x - y)`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < k ==> &0 < abs k`; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < k /\ k < d ==> abs k < d`] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `norm(x:real^N - y)` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LT_RMUL THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[NORM_SUB]] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < k /\ k < &1 ==> abs(&1 - k) < &1`) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_MUL_LZERO;
               REAL_MUL_LID]);;

let CLOSURE_BALL_FAN = prove
 (`!x:real^N e. &0 < e ==> (closure_fan(ball_fan(x,e)) = cball_fan(x,e))`,
  SIMP_TAC[EXTENSION; closure_fan; IN_ELIM_THM; IN_UNION; LIMPT_BALL_FAN] THEN
  REWRITE_TAC[IN_BALL_FAN; IN_CBALL_FAN] THEN REAL_ARITH_TAC);;

let INTERIOR_CBALL_FAN = prove
 (`!x:real^N e. &0 <= e ==> (interior_fan(cball_fan(x,e)) = ball_fan(x,e))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERIOR_UNIQUE_FAN THEN
  REWRITE_TAC[BALL_SUBSET_CBALL_FAN; OPEN_BALL_FAN] THEN
  X_GEN_TAC `t:real^N->bool` THEN
  SIMP_TAC[SUBSET; IN_CBALL_FAN; IN_BALL_FAN; REAL_LT_LE] THEN STRIP_TAC THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [open_def_fan]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `d:real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `z:real^N = x` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `k:real` o MATCH_MP REAL_DOWN) THEN
    SUBGOAL_THEN `?w:real^N. dist(w,x) = k` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[VECTOR_CHOOSE_DIST; DIST_SYM; REAL_LT_IMP_LE];
      ASM_MESON_TAC[REAL_NOT_LE; DIST_REFL; DIST_SYM]];
    RULE_ASSUM_TAC(REWRITE_RULE[DIST_NZ]) THEN
    DISCH_THEN(MP_TAC o SPEC `z + ((d / &2) / dist(z,x)) % (z - x:real^N)`) THEN
    REWRITE_TAC[dist; VECTOR_ADD_SUB; NORM_MUL; REAL_ABS_DIV;
                REAL_ABS_NORM; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; GSYM dist; REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    ASM_REWRITE_TAC[REAL_ARITH `abs d < d * &2 <=> &0 < d`] THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN REWRITE_TAC[dist] THEN
    REWRITE_TAC[VECTOR_ARITH `x - (z + k % (z - x)) = (&1 + k) % (x - z)`] THEN
    REWRITE_TAC[REAL_NOT_LE; NORM_MUL] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ; GSYM dist] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &1 < abs(&1 + x)`) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH]]);;

let FRONTIER_BALL_FAN = prove
 (`!a e. &0 < e
         ==> (frontier_fan(ball_fan(a,e)) = {x | dist(a,x) = e})`,
  SIMP_TAC[frontier_fan; CLOSURE_BALL_FAN; INTERIOR_OPEN_FAN; OPEN_BALL_FAN;
           REAL_LT_IMP_LE] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; IN_BALL_FAN; IN_CBALL_FAN] THEN
  REAL_ARITH_TAC);;

let FRONTIER_CBALL_FAN = prove
 (`!a e. &0 < e
         ==> (frontier_fan(cball_fan(a,e)) = {x | dist(a,x) = e})`,
  SIMP_TAC[frontier_fan; INTERIOR_CBALL_FAN; CLOSED_CBALL_FAN; CLOSURE_CLOSED_FAN;
           REAL_LT_IMP_LE] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; IN_BALL_FAN; IN_CBALL_FAN] THEN
  REAL_ARITH_TAC);;

let SUBSET_BALL_FAN = prove
 (`!x d e. d <= e ==> ball_fan(x,d) SUBSET ball_fan(x,e)`,
  REWRITE_TAC[SUBSET; IN_BALL_FAN] THEN MESON_TAC[REAL_LTE_TRANS]);;

let SUBSET_CBALL_FAN = prove
 (`!x d e. d <= e ==> cball_fan(x,d) SUBSET cball_fan(x,e)`,
  REWRITE_TAC[SUBSET; IN_CBALL_FAN] THEN MESON_TAC[REAL_LE_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Boundedness.                                                              *)
(* ------------------------------------------------------------------------- *)

let bounded_fan = new_definition
  `bounded_fan s <=> ?a. !x:real^N. x IN s ==> norm(x) <= a`;;

let BOUNDED_EMPTY_FAN = prove
 (`bounded_fan {}`,
  REWRITE_TAC[bounded_fan; NOT_IN_EMPTY]);;

let BOUNDED_SUBSET_FAN = prove
 (`!s t. bounded_fan t /\ s SUBSET t ==> bounded_fan s`,
  MESON_TAC[bounded_fan; SUBSET]);;

let BOUNDED_CLOSURE_FAN = prove
 (`!s:real^N->bool. bounded_fan s ==> bounded_fan(closure_fan s)`,
  REWRITE_TAC[bounded_fan; CLOSURE_SEQUENTIAL_FAN] THEN
  MESON_TAC[LIM_NORM_BOUND_FAN; TRIVIAL_LIMIT_SEQUENTIALLY_FAN; trivial_limit_fan]);;

let BOUNDED_CBALL_FAN = prove
 (`!x:real^N e. bounded_fan(cball_fan(x,e))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bounded_fan] THEN
  EXISTS_TAC `norm(x:real^N) + e` THEN REWRITE_TAC[IN_CBALL_FAN; dist] THEN
  MESON_TAC[NORM_SUB; NORM_TRIANGLE_SUB;
            REAL_ARITH `b <= c + a ==> a <= e ==> b <= c + e`]);;

let BOUNDED_BALL_FAN = prove
 (`!x e. bounded_fan(ball_fan(x,e))`,
  MESON_TAC[BALL_SUBSET_CBALL_FAN; BOUNDED_CBALL_FAN; BOUNDED_SUBSET_FAN]);;

let FINITE_IMP_BOUNDED_FAN = prove
 (`!s:real^N->bool. FINITE s ==> bounded_fan s`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[BOUNDED_EMPTY_FAN] THEN
  REWRITE_TAC[bounded_fan; IN_INSERT] THEN X_GEN_TAC `x:real^N` THEN GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`) STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `norm(x:real^N) + abs B` THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[NORM_POS_LE; REAL_ARITH
   `(y <= b /\ &0 <= x ==> y <= x + abs b) /\ x <= x + abs b`]);;

let BOUNDED_UNION_FAN = prove
 (`!s t. bounded_fan (s UNION t) <=> bounded_fan s /\ bounded_fan t`,
  REWRITE_TAC[bounded_fan; IN_UNION] THEN MESON_TAC[REAL_LE_MAX]);;

let BOUNDED_POS_FAN = prove
 (`!s. bounded_fan s <=> ?b. &0 < b /\ !x. x IN s ==> norm(x) <= b`,
  REWRITE_TAC[bounded_fan] THEN
  MESON_TAC[REAL_ARITH `&0 < &1 + abs(y) /\ (x <= y ==> x <= &1 + abs(y))`]);;

let BOUNDED_INTER_FAN = prove
 (`!s t. bounded_fan s \/ bounded_fan t ==> bounded_fan (s INTER t)`,
  MESON_TAC[BOUNDED_SUBSET_FAN; INTER_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Compactness (the definition is the one based on convegent subsequences).  *)
(* ------------------------------------------------------------------------- *)

let compact_fan = new_definition
  `compact_fan s <=>
        !f:num->real^N.
            (!n. f(n) IN s)
            ==> ?l r. l IN s /\ (!m n:num. m < n ==> r(m) < r(n)) /\
                      ((f o r) --> l) sequentially_fan`;;

let MONOTONE_BIGGER_FAN = prove
 (`!r. (!m n. m < n ==> r(m) < r(n)) ==> !n:num. n <= r(n)`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  ASM_MESON_TAC[LE_0; ARITH_RULE `n <= m /\ m < p ==> SUC n <= p`; LT]);;

let LIM_SUBSEQUENCE_FAN = prove
 (`!s r. (!m n. m < n ==> r(m) < r(n)) /\ (s --> l) sequentially_fan
         ==> (s o r --> l) sequentially_fan`,
  REWRITE_TAC[LIM_SEQUENTIALLY_FAN; o_THM] THEN
  MESON_TAC[MONOTONE_BIGGER_FAN; LE_TRANS]);;

let MONOTONE_SUBSEQUENCE_FAN = prove
 (`!s:num->real. ?r:num->num.
           (!m n. m < n ==> r(m) < r(n)) /\
           ((!m n. m <= n ==> s(r(m)) <= s(r(n))) \/
            (!m n. m <= n ==> s(r(n)) <= s(r(m))))`,
  GEN_TAC THEN
  ASM_CASES_TAC `!n:num. ?p. n < p /\ !m. p <= m ==> s(m) <= s(p)` THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; NOT_IMP; DE_MORGAN_THM] THEN
  REWRITE_TAC[RIGHT_OR_EXISTS_THM; SKOLEM_THM; REAL_NOT_LE; REAL_NOT_LT] THENL
   [ABBREV_TAC `N = 0`; DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC)] THEN
  DISCH_THEN(X_CHOOSE_THEN `next:num->num` STRIP_ASSUME_TAC) THEN
  (MP_TAC o prove_recursive_functions_exist num_RECURSION)
   `(r 0 = next(SUC N)) /\ (!n. r(SUC n) = next(r n))` THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `!m:num n:num. r n <= m ==> s(m) <= s(r n):real`
    ASSUME_TAC THEN TRY CONJ_TAC THEN TRY DISJ2_TAC THEN
    GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LT; LE] THEN
    ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL; LT_IMP_LE; LT_TRANS];
    SUBGOAL_THEN `!n. N < (r:num->num) n` ASSUME_TAC THEN
    TRY(CONJ_TAC THENL [GEN_TAC; DISJ1_TAC THEN GEN_TAC]) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[LT; LE] THEN
    TRY STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_LT_REFL; LT_LE; LTE_TRANS; REAL_LE_REFL;
                  REAL_LT_LE; REAL_LE_TRANS; LT]]);;

let CONVERGENT_BOUNDED_INCREASING_FAN = prove
 (`!s:num->real b. (!m n. m <= n ==> s m <= s n) /\ (!n. abs(s n) <= b)
                   ==> ?l. !e. &0 < e ==> ?N. !n. N <= n ==> abs(s n - l) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\x. ?n. (s:num->real) n = x` REAL_COMPLETE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_ARITH `abs(x) <= b ==> x <= b`]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l - e`) THEN
  ASM_MESON_TAC[REAL_ARITH `&0 < e ==> ~(l <= l - e)`;
      REAL_ARITH `x <= y /\ y <= l /\ ~(x <= l - e) ==> abs(y - l) < e`]);;

let CONVERGENT_BOUNDED_MONOTONE_FAN = prove
 (`!s:num->real b. (!n. abs(s n) <= b) /\
                   ((!m n. m <= n ==> s m <= s n) \/
                    (!m n. m <= n ==> s n <= s m))
                   ==> ?l. !e. &0 < e ==> ?N. !n. N <= n ==> abs(s n - l) < e`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[CONVERGENT_BOUNDED_INCREASING_FAN]; ALL_TAC] THEN
  MP_TAC(SPEC `\n. --((s:num->real) n)` CONVERGENT_BOUNDED_INCREASING_FAN) THEN
  ASM_REWRITE_TAC[REAL_LE_NEG2; REAL_ABS_NEG] THEN
  ASM_MESON_TAC[REAL_ARITH `abs(x - --l) = abs(--x - l)`]);;

let COMPACT_REAL_LEMMA_FAN = prove
 (`!s b. (!n:num. abs(s n) <= b)
         ==> ?l r. (!m n:num. m < n ==> r(m) < r(n)) /\
                   !e. &0 < e ==> ?N. !n. N <= n ==> abs(s(r n) - l) < e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MP_TAC(SPEC `s:num->real` MONOTONE_SUBSEQUENCE_FAN) THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC CONVERGENT_BOUNDED_MONOTONE_FAN THEN ASM_MESON_TAC[]);;

let COMPACT_LEMMA_FAN = prove
 (`!s. bounded_fan s /\ (!n. (x:num->real^N) n IN s)
       ==> !d. d <= dimindex(:N)
               ==> ?l:real^N r. (!m n. m < n ==> r m < (r:num->num) n) /\
                         !e. &0 < e
                             ==> ?N. !n i. 1 <= i /\ i <= d
                                           ==> N <= n
                                               ==> abs(x(r n)$i - l$i) < e`,
  GEN_TAC THEN REWRITE_TAC[bounded_fan] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `b:real`) ASSUME_TAC) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 0 <=> F`; CONJ_ASSOC] THEN
    DISCH_TAC THEN EXISTS_TAC `\n:num. n` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC d <= n ==> d <= n`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`\n:num. (x:num->real^N) (r n) $ (SUC d)`; `b:real`]
         COMPACT_REAL_LEMMA_FAN) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; COMPONENT_LE_NORM; ARITH_RULE `1 <= SUC n`];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real` (X_CHOOSE_THEN `s:num->num`
        STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`(lambda k. if k = SUC d then y else (l:real^N)$k):real^N`;
    `(r:num->num) o (s:num->num)`] THEN
  ASM_SIMP_TAC[o_THM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REPEAT(FIRST_ASSUM(C UNDISCH_THEN (MP_TAC o SPEC `e:real`) o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC `N1 + N2:num` THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[LAMBDA_BETA; MATCH_MP(ARITH_RULE
   `SUC d <= n ==> !i. 1 <= i /\ i <= SUC d ==> 1 <= i /\ i <= n`) th]) THEN
  REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN TRY COND_CASES_TAC THEN
  ASM_MESON_TAC[MONOTONE_BIGGER_FAN; LE_TRANS;
    ARITH_RULE `N1 + N2 <= n ==> N2 <= n:num /\ N1 <= n`;
    ARITH_RULE `1 <= i /\ i <= d /\ SUC d <= n
                ==> ~(i = SUC d) /\ 1 <= SUC d /\ d <= n /\ i <= n`]);;

let BOUNDED_CLOSED_IMP_COMPACT_FAN = prove
 (`!s:real^N->bool. bounded_fan s /\ closed_fan s ==> compact_fan s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[compact_fan] THEN
  X_GEN_TAC `x:num->real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` COMPACT_LEMMA_FAN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `dimindex(:N)`) THEN
  REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num->num` THEN ASM_SIMP_TAC[] THEN
  STRIP_TAC THEN MATCH_MP_TAC(TAUT `(b ==> a) /\ b ==> a /\ b`) THEN
  REPEAT STRIP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[CLOSED_SEQUENTIAL_LIMITS_FAN]) THEN
    EXISTS_TAC `(x:num->real^N) o (r:num->num)` THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY_FAN] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2 / &(dimindex(:N))`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; DIMINDEX_NONZERO;
               REAL_HALF; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  REWRITE_TAC[dist] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MATCH_MP (REAL_ARITH `a <= b ==> b < e ==> a < e`)
                        (SPEC_ALL NORM_LE_L1)) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sum (1..dimindex(:N))
                  (\k. e / &2 / &(dimindex(:N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN
    SIMP_TAC[o_THM; LAMBDA_BETA; vector_sub] THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE; LE_TRANS];
    ASM_SIMP_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_DIV_LMUL; REAL_OF_NUM_EQ;
                 DIMINDEX_NONZERO; REAL_LE_REFL; REAL_LT_LDIV_EQ; ARITH;
                 REAL_OF_NUM_LT; REAL_ARITH `x < x * &2 <=> &0 < x`]]);;

(* ------------------------------------------------------------------------- *)
(* Completeness.                                                             *)
(* ------------------------------------------------------------------------- *)

let cauchy_fan = new_definition
  `cauchy_fan (s:num->real^N) <=>
     !e. &0 < e ==> ?N. !m n. m >= N /\ n >= N ==> dist(s m,s n) < e`;;

let complete_fan = new_definition
  `complete_fan s <=>
     !f:num->real^N. (!n. f n IN s) /\ cauchy_fan f
                      ==> ?l. l IN s /\ (f --> l) sequentially_fan`;;

let CAUCHY_FAN = prove
 (`!s:num->real^N.
      cauchy_fan s <=> !e. &0 < e ==> ?N. !n. n >= N ==> dist(s n,s N) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cauchy_fan; GE] THEN EQ_TAC THENL
   [MESON_TAC[LE_REFL]; DISCH_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MESON_TAC[DIST_TRIANGLE_HALF_L]);;

let CONVERGENT_IMP_CAUCHY_FAN = prove
 (`!s l. (s --> l) sequentially_fan ==> cauchy_fan s`,
  REWRITE_TAC[LIM_SEQUENTIALLY_FAN; cauchy_fan] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  ASM_MESON_TAC[GE; LE_REFL; DIST_TRIANGLE_HALF_L]);;

let CAUCHY_IMP_BOUNDED_FAN = prove
 (`!s:num->real^N. cauchy_fan s ==> bounded_fan {y | ?n. y = s n}`,
  REWRITE_TAC[cauchy_fan; bounded_fan; IN_ELIM_THM] THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
  REWRITE_TAC[GE_REFL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!n:num. N <= n ==> norm(s n :real^N) <= norm(s N) + &1`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[GE; dist; DIST_SYM; NORM_TRIANGLE_SUB;
                  REAL_ARITH `a <= b + c /\ c < &1 ==> a <= b + &1`];
    MP_TAC(ISPECL [`\n:num. norm(s n :real^N)`; `0..N`]
                  UPPER_BOUND_FINITE_SET_REAL) THEN
    SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0; LEFT_IMP_EXISTS_THM] THEN
    ASM_MESON_TAC[LE_CASES;
                  REAL_ARITH `x <= a \/ x <= b ==> x <= abs a + abs b`]]);;


let COMPACT_IMP_COMPLETE_FAN = prove
 (`!s:real^N->bool. compact_fan s ==> complete_fan s`,
  GEN_TAC THEN REWRITE_TAC[complete_fan; compact_fan]
 THEN  MATCH_MP_TAC MONO_FORALL
 THEN X_GEN_TAC `f:num->real^N` 
  THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th)THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] LIM_ADD_FAN)) THEN
  DISCH_THEN(MP_TAC o SPEC `\n. (f:num->real^N)(n) - f(r n)`) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0: real^N`) THEN ASM_REWRITE_TAC[o_THM] THEN
  REWRITE_TAC[VECTOR_ADD_RID; VECTOR_SUB_ADD2; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cauchy_fan]) THEN
  REWRITE_TAC[GE; lim_fan; SEQUENTIALLY_FAN; dist; VECTOR_SUB_RZERO] THEN
  SUBGOAL_THEN `!n:num. n <= r(n)` MP_TAC THENL [INDUCT_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[ LE_TRANS; LE_REFL; LT; LET_TRANS; LE_0; LE_SUC_LT]);;

let COMPLETE_UNIV_FAN = prove
 (`complete_fan(:real^N)`,
  REWRITE_TAC[complete_fan; IN_UNIV] THEN X_GEN_TAC `x:num->real^N` THEN
  DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CAUCHY_IMP_BOUNDED_FAN) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP BOUNDED_CLOSURE_FAN) THEN
  MP_TAC(ISPEC `closure_fan {y:real^N | ?n:num. y = x n}`
               COMPACT_IMP_COMPLETE_FAN) THEN
  ASM_SIMP_TAC[BOUNDED_CLOSED_IMP_COMPACT_FAN; CLOSED_CLOSURE_FAN; complete_fan] THEN
  DISCH_THEN(MP_TAC o SPEC `x:num->real^N`) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  ASM_REWRITE_TAC[closure_fan; IN_ELIM_THM; IN_UNION] THEN MESON_TAC[]);;

let COMPLETE_EQ_CLOSED_FAN = prove
 (`!s:real^N->bool. complete_fan s <=> closed_fan s`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[complete_fan; CLOSED_LIMPT_FAN; LIMPT_SEQUENTIAL_FAN] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN GEN_TAC THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    MESON_TAC[CONVERGENT_IMP_CAUCHY_FAN; IN_DELETE; LIM_UNIQUE_FAN;
              TRIVIAL_LIMIT_SEQUENTIALLY_FAN];
    REWRITE_TAC[complete_fan; CLOSED_SEQUENTIAL_LIMITS_FAN] THEN DISCH_TAC THEN
    X_GEN_TAC `f:num->real^N` THEN STRIP_TAC THEN
    MP_TAC(REWRITE_RULE[complete_fan] COMPLETE_UNIV_FAN) THEN
    DISCH_THEN(MP_TAC o SPEC `f:num->real^N`) THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN ASM_MESON_TAC[]]);;

let CONVERGENT_EQ_CAUCHY_FAN = prove
 (`!s. (?l. (s --> l) sequentially_fan) <=> cauchy_fan s`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM; CONVERGENT_IMP_CAUCHY_FAN];
    REWRITE_TAC[REWRITE_RULE[complete_fan; IN_UNIV] COMPLETE_UNIV_FAN]]);;

(* ------------------------------------------------------------------------- *)
(* Total boundedness.                                                        *)
(* ------------------------------------------------------------------------- *)

let COMPACT_IMP_TOTALLY_BOUNDED_FAN = prove
 (`!s:real^N->bool.
        compact_fan s
        ==> !e. &0 < e ==> ?k. FINITE k /\ k SUBSET s /\
                               s SUBSET (UNIONS(IMAGE (\x. ball_fan(x,e)) k))`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`; SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?x:num->real^N. !n. x(n) IN s /\ !m. m < n ==> ~(dist(x(m),x(n)) < e)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `?x:num->real^N.
          !n. x(n) = @y. y IN s /\ !m. m < n ==> ~(dist(x(m),y) < e)`
    MP_TAC THENL
     [MATCH_MP_TAC(MATCH_MP WF_REC WF_num) THEN SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:num->real^N` THEN
    DISCH_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SPEC `n:num`) THEN STRIP_TAC THEN
    CONV_TAC SELECT_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (x:num->real^N) {m | m < n}`) THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT; NOT_FORALL_THM; NOT_IMP] THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[IN_BALL_FAN];
    ALL_TAC] THEN
  REWRITE_TAC[compact_fan; NOT_FORALL_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x:num->real^N` THEN  REWRITE_TAC[NOT_IMP; FORALL_AND_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP CONVERGENT_IMP_CAUCHY_FAN) THEN
  REWRITE_TAC[cauchy_fan] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[o_THM; NOT_EXISTS_THM; NOT_IMP; NOT_FORALL_THM; NOT_IMP] THEN
  X_GEN_TAC `N:num` THEN MAP_EVERY EXISTS_TAC [`N:num`; `SUC N`] THEN
  CONJ_TAC THENL [ARITH_TAC; ASM_MESON_TAC[LT]]);;

(* ------------------------------------------------------------------------- *)
(* Heine-Borel theorem (following Burkill & Burkill vol. 2)                  *)
(* ------------------------------------------------------------------------- *)

let HEINE_BOREL_LEMMA_FAN = prove
 (`!s:real^N->bool.
      compact_fan s
      ==> !t. s SUBSET (UNIONS t) /\ (!b. b IN t ==> open_fan b)
              ==> ?e. &0 < e /\
                      !x. x IN s ==> ?b. b IN t /\ ball_fan(x,e) SUBSET b`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&1 / (&n + &1)`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_LT_01; REAL_ARITH `x <= y ==> x < y + &1`;
   FORALL_AND_THM; REAL_POS; NOT_FORALL_THM; NOT_IMP; SKOLEM_THM; compact_fan] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`l:real^N`; `r:num->num`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?b:real^N->bool. l IN b /\ b IN t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; IN_UNIONS]; ALL_TAC] THEN
  SUBGOAL_THEN `?e. &0 < e /\ !z:real^N. dist(z,l) < e ==> z IN b`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[open_def_fan]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY_FAN]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  SUBGOAL_THEN `&0 < e / &2` (fun th ->
    REWRITE_TAC[th; o_THM] THEN MP_TAC(GEN_REWRITE_RULE I [REAL_ARCH_INV] th))
  THENL [ASM_REWRITE_TAC[REAL_HALF]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(r:num->num)(N1 + N2)`; `b:real^N->bool`]) THEN
  ASM_REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC DIST_TRIANGLE_HALF_R THEN
  EXISTS_TAC `(f:num->real^N)(r(N1 + N2:num))` THEN CONJ_TAC THENL
   [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL_FAN]) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x < a ==> x < b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&N1)` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
  ASM_MESON_TAC[ARITH_RULE `(~(n = 0) ==> 0 < n)`; LE_ADD; MONOTONE_BIGGER_FAN;
                LT_IMP_LE; LE_TRANS]);;

let COMPACT_IMP_HEINE_BOREL_FAN = prove
 (`!s. compact_fan (s:real^N->bool)
       ==> !f. (!t. t IN f ==> open_fan t) /\ s SUBSET (UNIONS f)
               ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET (UNIONS f')`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `f:(real^N->bool)->bool` o
    MATCH_MP HEINE_BOREL_LEMMA_FAN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; SUBSET; IN_BALL_FAN] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real^N->real^N->bool`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `e:real` o
    MATCH_MP COMPACT_IMP_TOTALLY_BOUNDED_FAN) THEN
  ASM_REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE; IN_BALL_FAN] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (B:real^N->real^N->bool) k` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  ASM_MESON_TAC[IN_BALL_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Bolzano-Weierstrass property.                                             *)
(* ------------------------------------------------------------------------- *)

let HEINE_BOREL_IMP_BOLZANO_WEIERSTRASS_FAN = prove
 (`!s:real^N->bool.
        (!f. (!t. t IN f ==> open_fan t) /\ s SUBSET (UNIONS f)
             ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET (UNIONS f'))
        ==> !t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of_fan t`,
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; limit_point_of_fan] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b /\ c ==> d <=> c ==> ~d ==> a ==> ~b`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; RIGHT_AND_FORALL_THM] THEN
  DISCH_TAC THEN REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `f:real^N->real^N->bool`) THEN
  DISCH_THEN(MP_TAC o SPEC
   `{t:real^N->bool | ?x:real^N. x IN s /\ (t = f x)}`) THEN
  REWRITE_TAC[INFINITE; SUBSET; IN_ELIM_THM; IN_UNIONS; NOT_IMP] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:real^N | x IN t /\ (f(x):real^N->bool) IN g}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ_GENERAL THEN ASM_MESON_TAC[SUBSET];
    SIMP_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `u:real^N` THEN
    DISCH_TAC THEN SUBGOAL_THEN `(u:real^N) IN s` ASSUME_TAC THEN
    ASM_MESON_TAC[SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Complete the chain of compactness variants.                               *)
(* ------------------------------------------------------------------------- *)

let BOLZANO_WEIERSTRASS_IMP_BOUNDED_FAN = prove
 (`!s:real^N->bool.
        (!t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of_fan t)
        ==> bounded_fan s`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  SIMP_TAC[compact_fan; bounded_fan] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM; SKOLEM_THM; NOT_IMP] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_THEN(X_CHOOSE_TAC `beyond:real->real^N`) THEN
  (MP_TAC o prove_recursive_functions_exist num_RECURSION)
   `(f(0) = beyond(&0)) /\
    (!n. f(SUC n) = beyond(norm(f n) + &1):real^N)` THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (x:num->real^N) UNIV` THEN
  SUBGOAL_THEN
   `!m n. m < n ==> norm((x:num->real^N) m) + &1 < norm(x n)`
  ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LT] THEN
    ASM_MESON_TAC[REAL_LT_TRANS; REAL_ARITH `b < b + &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. ~(m = n) ==> &1 < dist((x:num->real^N) m,x n)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (SPECL [`m:num`; `n:num`] LT_CASES) THEN
    ASM_MESON_TAC[dist; LT_CASES; NORM_TRIANGLE_SUB; NORM_SUB;
                  REAL_ARITH `x + &1 < y /\ y <= x + d ==> &1 < d`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[INFINITE_IMAGE_INJ; num_INFINITE; DIST_REFL;
                  REAL_ARITH `~(&1 < &0)`];
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
    GEN_TAC THEN INDUCT_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `l:real^N` THEN REWRITE_TAC[LIMPT_APPROACHABLE_FAN] THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIV; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `&1 / &2`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `dist((x:num->real^N) k,l)`) THEN
  ASM_SIMP_TAC[DIST_POS_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `m:num = k` THEN
  ASM_MESON_TAC[DIST_TRIANGLE_HALF_L; REAL_LT_TRANS; REAL_LT_REFL]);;

let SEQUENCE_INFINITE_LEMMA_FAN = prove
 (`!f l. (!n. ~(f(n) = l)) /\ (f --> l) sequentially_fan
         ==> INFINITE {y:real^N | ?n. y = f n}`,
  REWRITE_TAC[INFINITE] THEN REPEAT STRIP_TAC THEN MP_TAC(ISPEC
   `IMAGE (\y:real^N. dist(y,l)) {y | ?n:num. y = f n}` INF_FINITE) THEN
  ASM_SIMP_TAC[GSYM MEMBER_NOT_EMPTY; IN_IMAGE; FINITE_IMAGE; IN_ELIM_THM] THEN
  ASM_MESON_TAC[LIM_SEQUENTIALLY_FAN; LE_REFL; REAL_NOT_LE; DIST_POS_LT]);;

let SEQUENCE_UNIQUE_LIMPT_FAN = prove
 (`!f l. (!n. ~(f(n) = l)) /\ (f --> l) sequentially_fan
         ==> !l'. l' limit_point_of_fan {y:real^N | ?n. y = f n}
                  ==> (l' = l)`,
  REWRITE_TAC[LIMPT_APPROACHABLE_FAN; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  REPEAT STRIP_TAC THEN ABBREV_TAC `e = dist(l':real^N,l)` THEN
  SUBGOAL_THEN `~(&0 < e)` (fun th -> ASM_MESON_TAC[th; DIST_POS_LT]) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY_FAN]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN MP_TAC(ISPEC  
   `(e / &2) INSERT
    (IMAGE (\n. if dist((f:num->real^N) n,l') = &0 then e / &2
                else dist((f:num->real^N) n,l'))
           {n | n < N})`
 INF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_RULES; FINITE_IMAGE; FINITE_NUMSEG_LT;
	                     NOT_EMPTY_INSERT] THEN
  ABBREV_TAC(mk_eq(`d:real`,mk_comb(`inf`,  
   `(e / &2) INSERT
    (IMAGE (\n. if dist((f:num->real^N) n,l') = &0 then e / &2
                else dist((f:num->real^N) n,l'))
           {n | n < N})`
))) THEN
  REWRITE_TAC[IN_INSERT; IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    REPEAT COND_CASES_TAC THEN
    ASM_MESON_TAC[REAL_HALF; REAL_LT_LE; DIST_POS_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `e / &2` th) THEN
                   MP_TAC(SPEC `dist((f:num->real^N) k,l')` th)) THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LT; DE_MORGAN_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[DIST_EQ_0; NOT_LT; GSYM REAL_NOT_LE] THEN
  ASM_MESON_TAC[DIST_TRIANGLE_HALF_R; REAL_LT_REFL; REAL_LTE_TRANS]);;

let BOLZANO_WEIERSTRASS_IMP_CLOSED_FAN = prove
 (`!s:real^N->bool.
        (!t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of_fan t)
        ==> closed_fan s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSED_SEQUENTIAL_LIMITS_FAN] THEN
  MAP_EVERY X_GEN_TAC [`f:num->real^N`; `l:real^N`] THEN
  DISCH_TAC THEN
  MAP_EVERY (MP_TAC o ISPECL [`f:num->real^N`; `l:real^N`])
   [SEQUENCE_UNIQUE_LIMPT_FAN; SEQUENCE_INFINITE_LEMMA_FAN] THEN
  MATCH_MP_TAC(TAUT
   `(~d ==> a /\ ~(b /\ c)) ==> (a ==> b) ==> (a ==> c) ==> d`) THEN
  DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{y:real^N | ?n:num. y = f n}`) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM];
    ABBREV_TAC `t = {y:real^N | ?n:num. y = f n}`] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence express everything as an equivalence.                               *)
(* ------------------------------------------------------------------------- *)

let COMPACT_EQ_HEINE_BOREL_FAN = prove
 (`!s:real^N->bool.
        compact_fan s <=>
           !f. (!t. t IN f ==> open_fan t) /\ s SUBSET (UNIONS f)
               ==> ?f'. f' SUBSET f /\ FINITE f' /\ s SUBSET (UNIONS f')`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[COMPACT_IMP_HEINE_BOREL_FAN] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HEINE_BOREL_IMP_BOLZANO_WEIERSTRASS_FAN) THEN
  DISCH_TAC THEN MATCH_MP_TAC BOUNDED_CLOSED_IMP_COMPACT_FAN THEN
  ASM_SIMP_TAC[BOLZANO_WEIERSTRASS_IMP_BOUNDED_FAN;
               BOLZANO_WEIERSTRASS_IMP_CLOSED_FAN]);;




let COMPACT_EQ_BOLZANO_WEIERSTRASS_FAN = prove
 (`!s:real^N->bool.
        compact_fan s <=>
           !t. INFINITE t /\ t SUBSET s ==> ?x. x IN s /\ x limit_point_of_fan t`,
  GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[COMPACT_EQ_HEINE_BOREL_FAN; HEINE_BOREL_IMP_BOLZANO_WEIERSTRASS_FAN];
    SIMP_TAC[BOLZANO_WEIERSTRASS_IMP_BOUNDED_FAN; BOLZANO_WEIERSTRASS_IMP_CLOSED_FAN;
             BOUNDED_CLOSED_IMP_COMPACT_FAN]]);;

let COMPACT_EQ_BOUNDED_CLOSED_FAN = prove
 (`!s:real^N->bool. compact_fan s <=> bounded_fan s /\ closed_fan s`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[BOUNDED_CLOSED_IMP_COMPACT_FAN] THEN
  SIMP_TAC[COMPACT_EQ_BOLZANO_WEIERSTRASS_FAN; BOLZANO_WEIERSTRASS_IMP_BOUNDED_FAN;
           BOLZANO_WEIERSTRASS_IMP_CLOSED_FAN]);;

let COMPACT_IMP_BOUNDED_FAN = prove
 (`!s. compact_fan s ==> bounded_fan s`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN]);;

let COMPACT_IMP_CLOSED_FAN = prove
 (`!s. compact_fan s ==> closed_fan s`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN]);;

(* ------------------------------------------------------------------------- *)
(* In particular, some common special cases.                                 *)
(* ------------------------------------------------------------------------- *)

let COMPACT_EMPTY_FAN = prove
 (`compact_fan {}`,
  REWRITE_TAC[compact_fan; NOT_IN_EMPTY]);;

let COMPACT_UNION_FAN = prove
 (`!s t. compact_fan s /\ compact_fan t ==> compact_fan (s UNION t)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN; BOUNDED_UNION_FAN; CLOSED_UNION_FAN]);;

let COMPACT_INTER_FAN = prove
 (`!s t. compact_fan s /\ compact_fan t ==> compact_fan (s INTER t)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN; BOUNDED_INTER_FAN; CLOSED_INTER_FAN]);;

let COMPACT_INTER_CLOSED_FAN = prove
 (`!s t. compact_fan s /\ closed_fan t ==> compact_fan (s INTER t)`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN; CLOSED_INTER_FAN] THEN
  MESON_TAC[BOUNDED_SUBSET_FAN; INTER_SUBSET]);;

let CLOSED_INTER_COMPACT_FAN = prove
 (`!s t. closed_fan s /\ compact_fan t ==> compact_fan (s INTER t)`,
  MESON_TAC[COMPACT_INTER_CLOSED_FAN; INTER_COMM]);;

let FINITE_IMP_CLOSED_FAN = prove
 (`!s. FINITE s ==> closed_fan s`,
  MESON_TAC[BOLZANO_WEIERSTRASS_IMP_CLOSED_FAN; INFINITE; FINITE_SUBSET]);;

let FINITE_IMP_COMPACT_FAN = prove
 (`!s. FINITE s ==> compact_fan s`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN; FINITE_IMP_CLOSED_FAN; FINITE_IMP_BOUNDED_FAN]);;

let COMPACT_SING_FAN = prove
 (`!a. compact_fan {a}`,
  SIMP_TAC[FINITE_IMP_COMPACT_FAN; FINITE_RULES]);;

let CLOSED_SING_FAN = prove
 (`!a. closed_fan {a}`,
  MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN; COMPACT_SING_FAN]);;

let COMPACT_CBALL_FAN = prove
 (`!x e. compact_fan(cball_fan(x,e))`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN; BOUNDED_CBALL_FAN; CLOSED_CBALL_FAN]);;

let COMPACT_FRONTIER_BOUNDED_FAN = prove
 (`!s. bounded_fan s ==> compact_fan(frontier_fan s)`,
  SIMP_TAC[frontier_fan; COMPACT_EQ_BOUNDED_CLOSED_FAN;
           CLOSED_DIFF_FAN; OPEN_INTERIOR_FAN; CLOSED_CLOSURE_FAN] THEN
  MESON_TAC[SUBSET_DIFF; BOUNDED_SUBSET_FAN; BOUNDED_CLOSURE_FAN]);;

let COMPACT_FRONTIER_FAN = prove
 (`!s. compact_fan s ==> compact_fan (frontier_fan s)`,
  MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN; COMPACT_FRONTIER_BOUNDED_FAN]);;

let FRONTIER_SUBSET_COMPACT_FAN = prove
 (`!s. compact_fan s ==> frontier_fan s SUBSET s`,
  MESON_TAC[FRONTIER_SUBSET_CLOSED_FAN; COMPACT_EQ_BOUNDED_CLOSED_FAN]);;

let open_delete_fan = prove(`s DELETE x = s DIFF {x}`,SET_TAC[]);;

let OPEN_DELETE_FAN = prove
 (`!s x. open_fan s ==> open_fan(s DELETE x)`,
  
  SIMP_TAC[ open_delete_fan; OPEN_DIFF_FAN; CLOSED_SING_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Finite intersection property. I could make it an equivalence in fact.     *)
(* ------------------------------------------------------------------------- *)
  let compact_imp_fip_fan = prove(`(s = UNIV DIFF t) <=> (UNIV DIFF s = t)`,SET_TAC[]);;

let COMPACT_IMP_FIP_FAN = prove
 (`!s:real^N->bool f.
        compact_fan s /\
        (!t. t IN f ==> closed_fan t) /\
        (!f'. FINITE f' /\ f' SUBSET f ==> ~(s INTER (INTERS f') = {}))
        ==> ~(s INTER (INTERS f) = {})`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL_FAN]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (\t:real^N->bool. UNIV DIFF t) f`) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE] THEN
  DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[OPEN_DIFF_FAN; CLOSED_DIFF_FAN; OPEN_UNIV_FAN; CLOSED_UNIV_FAN; NOT_IMP] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) INTER INTERS f = {}` THEN
    ONCE_REWRITE_TAC[SUBSET; EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` MP_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (\t:real^N->bool. UNIV DIFF t) g`) THEN
    ASM_CASES_TAC `FINITE(g:(real^N->bool)->bool)` THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN ONCE_REWRITE_TAC[SUBSET; EXTENSION] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; IN_INTERS; IN_IMAGE; IN_DIFF;
                IN_UNIV; NOT_IN_EMPTY;  compact_imp_fip_fan; UNWIND_THM1; IN_UNIONS] THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Bounded closed nest property (proof does not use Heine-Borel).            *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_CLOSED_NEST_FAN = prove
 (`!s. (!n. closed_fan(s n)) /\ (!n. ~(s n = {})) /\
       (!m n. m <= n ==> s(n) SUBSET s(m)) /\
       bounded_fan(s 0)
       ==> ?a:real^N. !n:num. a IN s(n)`,
  GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `a:num->real^N`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `compact_fan(s 0:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[BOUNDED_CLOSED_IMP_COMPACT_FAN]; ALL_TAC] THEN
  REWRITE_TAC[compact_fan] THEN
  DISCH_THEN(MP_TAC o SPEC `a:num->real^N`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; LE_0]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^N` THEN
  REWRITE_TAC[LIM_SEQUENTIALLY_FAN; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num->num` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC I [TAUT `p <=> ~(~p)`] THEN
  GEN_REWRITE_TAC RAND_CONV [NOT_FORALL_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` MP_TAC) THEN
  MP_TAC(ISPECL [`l:real^N`; `(s:num->real^N->bool) N`]
                CLOSED_APPROACHABLE_FAN) THEN
  ASM_MESON_TAC[SUBSET; LE_REFL; LE_TRANS; LE_CASES; MONOTONE_BIGGER_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Decreasing case does not even need compactness, just completeness.        *)
(* ------------------------------------------------------------------------- *)

let DECREASING_CLOSED_NEST_FAN = prove
 (`!s. (!n. closed_fan(s n)) /\ (!n. ~(s n = {})) /\
       (!m n. m <= n ==> s(n) SUBSET s(m)) /\
       (!e. &0 < e ==> ?n. !x y. x IN s(n) /\ y IN s(n) ==> dist(x,y) < e)
       ==> ?a:real^N. !n:num. a IN s(n)`,
  GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `a:num->real^N`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?l:real^N. (a --> l) sequentially_fan` MP_TAC THENL
   [ASM_MESON_TAC[cauchy_fan; GE; SUBSET; LE_TRANS; LE_REFL;
                  complete_fan; COMPLETE_UNIV_FAN; IN_UNIV];
    ASM_MESON_TAC[LIM_SEQUENTIALLY_FAN; CLOSED_APPROACHABLE_FAN;
                  SUBSET; LE_REFL; LE_TRANS; LE_CASES]]);;

(* ------------------------------------------------------------------------- *)
(* Strengthen it to the intersection actually being a singleton.             *)
(* ------------------------------------------------------------------------- *)

let DECREASING_CLOSED_NEST_SING_FAN = prove
 (`!s. (!n. closed_fan(s n)) /\ (!n. ~(s n = {})) /\
       (!m n. m <= n ==> s(n) SUBSET s(m)) /\
       (!e. &0 < e ==> ?n. !x y. x IN s(n) /\ y IN s(n) ==> dist(x,y) < e)
       ==> ?a:real^N. INTERS {t | ?n:num. t = s n} = {a}`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DECREASING_CLOSED_NEST_FAN) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^N` THEN
  DISCH_TAC THEN REWRITE_TAC[EXTENSION; IN_INTERS; IN_SING; IN_ELIM_THM] THEN
  ASM_MESON_TAC[DIST_POS_LT; REAL_LT_REFL; SUBSET; LE_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Define continuity over a net to take in restrictions of the set.          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("continuous_fan",(12,"right"));;

let continuous_fan = new_definition
  `f continuous_fan net_fan <=> (f --> f(netlimit_fan net_fan)) net_fan`;;

let CONTINUOUS_WITHIN_FAN = prove
 (`!f x:real^M. f continuous_fan (at_fan x within_fan s) <=> (f --> f(x)) (at_fan x within_fan s)`,
REPEAT GEN_TAC THEN REWRITE_TAC[continuous_fan]
THEN ASM_CASES_TAC `trivial_limit_fan(at_fan (x:real^M) within_fan s)` THENL
   [ASM_REWRITE_TAC[lim_fan]; ASM_SIMP_TAC[NETLIMIT_WITHIN_FAN]]);;

let CONTINUOUS_AT_FAN = prove
 (`!f (x:real^N). f continuous_fan (at_fan x) <=> (f --> f(x)) (at_fan x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV_FAN] THEN
  REWRITE_TAC[CONTINUOUS_WITHIN_FAN; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Derive the epsilon-delta forms, which we often use as "definitions"       *)
(* ------------------------------------------------------------------------- *)

let continuous_within_fan = prove
 (`f continuous_fan (at_fan x within_fan s) <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x'. x' IN s /\ dist(x',x) < d ==> dist(f(x'),f(x)) < e`,
  REWRITE_TAC[CONTINUOUS_WITHIN_FAN; LIM_WITHIN_FAN] THEN
  REWRITE_TAC[GSYM DIST_NZ] THEN MESON_TAC[DIST_REFL]);;

let continuous_at_fan = prove
 (`f continuous_fan (at_fan x) <=>
        !e. &0 < e ==> ?d. &0 < d /\
                           !x'. dist(x',x) < d ==> dist(f(x'),f(x)) < e`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV_FAN] THEN
  REWRITE_TAC[continuous_within_fan; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* For setwise continuity, just start from the epsilon-delta definitions.    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("continuous_on_fan",(12,"right"));;
parse_as_infix ("uniformly_continuous_on_fan",(12,"right"));;

let continuous_on_fan = new_definition
  `f continuous_on_fan s <=>
        !x. x IN s ==> !e. &0 < e
                           ==> ?d. &0 < d /\
                                   !x'. x' IN s /\ dist(x',x) < d
                                        ==> dist(f(x'),f(x)) < e`;;

let uniformly_continuous_on_fan = new_definition
  `f uniformly_continuous_on_fan s <=>
        !e. &0 < e
            ==> ?d. &0 < d /\
                    !x x'. x IN s /\ x' IN s /\ dist(x',x) < d
                           ==> dist(f(x'),f(x)) < e`;;

(* ------------------------------------------------------------------------- *)
(* Some simple consequential lemmas.                                         *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS_FAN = prove
 (`!f s. f uniformly_continuous_on_fan s ==> f continuous_on_fan s`,
  REWRITE_TAC[uniformly_continuous_on_fan; continuous_on_fan] THEN MESON_TAC[]);;

let CONTINUOUS_AT_IMP_CONTINUOUS_WITHIN_FAN = prove
 (`!f s x. f continuous_fan (at_fan x) ==> f continuous_fan (at_fan x within_fan s)`,
  SIMP_TAC[LIM_AT_WITHIN_FAN; CONTINUOUS_AT_FAN; CONTINUOUS_WITHIN_FAN]);;

let CONTINUOUS_AT_IMP_CONTINUOUS_ON_FAN = prove
 (`!f s. (!x. x IN s ==> f continuous_fan (at_fan x)) ==> f continuous_on_fan s`,
  REWRITE_TAC[continuous_at_fan; continuous_on_fan] THEN MESON_TAC[]);;

let CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN_FAN = prove
 (`!f s. f continuous_on_fan s <=> !x. x IN s ==> f continuous_fan (at_fan x within_fan s)`,
  REWRITE_TAC[continuous_on_fan; continuous_within_fan]);;

let CONTINUOUS_ON_FAN = prove
 (`!f (s:real^N->bool).
        f continuous_on_fan s <=> !x. x IN s ==> (f --> f(x)) (at_fan x within_fan s)`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN_FAN; CONTINUOUS_WITHIN_FAN]);;

let CONTINUOUS_ON_EQ_CONTINUOUS_AT_FAN = prove
 (`!f:real^M->real^N s.
  open_fan s ==> (f continuous_on_fan s <=> (!x. x IN s ==> f continuous_fan (at_fan x)))`,
  SIMP_TAC[CONTINUOUS_ON_FAN; CONTINUOUS_AT_FAN; LIM_WITHIN_OPEN_FAN]);;

let CONTINUOUS_WITHIN_SUBSET_FAN = prove
 (`!f s t x. f continuous_fan (at_fan x within_fan s) /\ t SUBSET s
             ==> f continuous_fan (at_fan x within_fan t)`,
   REWRITE_TAC[CONTINUOUS_WITHIN_FAN] THEN MESON_TAC[LIM_WITHIN_SUBSET_FAN]);;

let CONTINUOUS_ON_SUBSET_FAN = prove
 (`!f s t. f continuous_on_fan s /\ t SUBSET s ==> f continuous_on_fan t`,
  REWRITE_TAC[CONTINUOUS_ON_FAN] THEN MESON_TAC[SUBSET; LIM_WITHIN_SUBSET_FAN]);;

let CONTINUOUS_ON_INTERIOR_FAN = prove
 (`!f:real^M->real^N s x.
        f continuous_on_fan s /\ x IN interior_fan(s) ==> f continuous_fan at_fan x`,
  REWRITE_TAC[interior_fan; IN_ELIM_THM] THEN
  MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT_FAN; CONTINUOUS_ON_SUBSET_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Characterization of various kinds of continuity in terms of sequences.    *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_SEQUENTIALLY_FAN = prove
 (`!f a:real^N.
        f continuous_fan (at_fan a within_fan s) <=>
                !x. (!n. x(n) IN s) /\ (x --> a) sequentially_fan
                     ==> ((f o x) --> f(a)) sequentially_fan`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_within_fan] THEN EQ_TAC THENL
   [REWRITE_TAC[LIM_SEQUENTIALLY_FAN; o_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&1 / (&n + &1)`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_POS; ARITH;
       REAL_ARITH `&0 <= n ==> &0 < n + &1`; NOT_FORALL_THM; SKOLEM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[NOT_IMP; FORALL_AND_THM] THEN
  X_GEN_TAC `y:num->real^N` THEN REWRITE_TAC[LIM_SEQUENTIALLY_FAN; o_THM] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[LE_REFL]] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FORALL_POS_MONO_1 THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `&1 / (&m + &1)` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_LE_INV2; real_div; REAL_ARITH `&0 <= x ==> &0 < x + &1`;
               REAL_POS; REAL_MUL_LID; REAL_LE_RADD; REAL_OF_NUM_LE]);;

let CONTINUOUS_AT_SEQUENTIALLY_FAN = prove
 (`!f a:real^N.
        f continuous_fan (at_fan a) <=>
              !x. (x --> a) sequentially_fan
                  ==> ((f o x) --> f(a)) sequentially_fan`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV_FAN] THEN
  REWRITE_TAC[CONTINUOUS_WITHIN_SEQUENTIALLY_FAN; IN_UNIV]);;

let CONTINUOUS_ON_SEQUENTIALLY_FAN = prove
 (`!f s:real^N->bool.
        f continuous_on_fan s <=>
              !x a. a IN s /\ (!n. x(n) IN s) /\ (x --> a) sequentially_fan
                    ==> ((f o x) --> f(a)) sequentially_fan`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN_FAN;
              CONTINUOUS_WITHIN_SEQUENTIALLY_FAN] THEN MESON_TAC[]);;

let UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY_FAN = prove
 (`!f s:real^N->bool.
        f uniformly_continuous_on_fan s <=>
              !x y. (!n. x(n) IN s) /\ (!n. y(n) IN s) /\
                    ((\n. x(n) - y(n)) --> vec 0) sequentially_fan
                    ==> ((\n. f(x(n)) - f(y(n))) --> vec 0) sequentially_fan`,
  REPEAT GEN_TAC THEN REWRITE_TAC[uniformly_continuous_on_fan] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY_FAN; dist; VECTOR_SUB_RZERO] THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `&1 / (&n + &1)`) THEN
  SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_POS; ARITH;
       REAL_ARITH `&0 <= n ==> &0 < n + &1`; NOT_FORALL_THM; SKOLEM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:num->real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:num->real^N` THEN
  REWRITE_TAC[NOT_IMP; FORALL_AND_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FORALL_POS_MONO_1 THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&1 / (&m + &1)` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_INV2; real_div; REAL_ARITH `&0 <= x ==> &0 < x + &1`;
                 REAL_POS; REAL_MUL_LID; REAL_LE_RADD; REAL_OF_NUM_LE];
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `\x:num. x` THEN ASM_REWRITE_TAC[LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Combination results for pointwise continuity.                             *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_CONST_FAN = prove
 (`!net c. (\x. c) continuous_fan net_fan`,
  REWRITE_TAC[continuous_fan; LIM_CONST_FAN]);;

let CONTINUOUS_CMUL_FAN = prove
 (`!f c net. f continuous_fan net_fan ==> (\x. c % f(x)) continuous_fan net_fan`,
  REWRITE_TAC[continuous_fan; LIM_CMUL_FAN]);;

let CONTINUOUS_NEG_FAN = prove
 (`!f net. f continuous_fan net_fan ==> (\x. --(f x)) continuous_fan net_fan`,
  REWRITE_TAC[continuous_fan; LIM_NEG_FAN]);;

let CONTINUOUS_ADD_FAN = prove
 (`!f g net. f continuous_fan net_fan /\ g continuous_fan net_fan
           ==> (\x. f(x) + g(x)) continuous_fan net_fan`,
  REWRITE_TAC[continuous_fan; LIM_ADD_FAN]);;

let CONTINUOUS_SUB_FAN = prove
 (`!f g net. f continuous_fan net_fan /\ g continuous_fan net_fan
           ==> (\x. f(x) - g(x)) continuous_fan net_fan`,
  REWRITE_TAC[continuous_fan; LIM_SUB_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Same thing for setwise continuity.                                        *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_CONST_FAN = prove
 (`!s c. (\x. c) continuous_on_fan s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN_FAN; CONTINUOUS_CONST_FAN]);;

let CONTINUOUS_ON_CMUL_FAN = prove
 (`!f c s. f continuous_on_fan s ==> (\x. c % f(x)) continuous_on_fan s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN_FAN; CONTINUOUS_CMUL_FAN]);;

let CONTINUOUS_ON_NEG_FAN = prove
 (`!f s. f continuous_on_fan s
         ==> (\x. --(f x)) continuous_on_fan s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN_FAN; CONTINUOUS_NEG_FAN]);;

let CONTINUOUS_ON_ADD_FAN = prove
 (`!f g s. f continuous_on_fan s /\ g continuous_on_fan s
           ==> (\x. f(x) + g(x)) continuous_on_fan s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN_FAN; CONTINUOUS_ADD_FAN]);;

let CONTINUOUS_ON_SUB_FAN = prove
 (`!f g s. f continuous_on_fan s /\ g continuous_on_fan s
           ==> (\x. f(x) - g(x)) continuous_on_fan s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN_FAN; CONTINUOUS_SUB_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Same thing for uniform continuity, using sequential formulations.         *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONTINUOUS_ON_CONST_FAN = prove
 (`!s c. (\x. c) uniformly_continuous_on_fan s`,
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY_FAN; o_DEF;
              VECTOR_SUB_REFL; LIM_CONST_FAN]);;

let UNIFORMLY_CONTINUOUS_ON_CMUL_FAN = prove
 (`!f c s. f uniformly_continuous_on_fan s
           ==> (\x. c % f(x)) uniformly_continuous_on_fan s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY_FAN] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_CMUL_FAN) THEN
  ASM_SIMP_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_RZERO]);;

let UNIFORMLY_CONTINUOUS_ON_NEG_FAN = prove
 (`!f s. f uniformly_continuous_on_fan s
         ==> (\x. --(f x)) uniformly_continuous_on_fan s`,
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_CMUL_FAN]);;

let UNIFORMLY_CONTINUOUS_ON_ADD_FAN = prove
 (`!f g s. f uniformly_continuous_on_fan s /\ g uniformly_continuous_on_fan s
           ==> (\x. f(x) + g(x)) uniformly_continuous_on_fan s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_SEQUENTIALLY_FAN] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD_FAN) THEN
  MATCH_MP_TAC EQ_IMP THEN
  REWRITE_TAC[VECTOR_ADD_LID] THEN AP_THM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC);;

let UNIFORMLY_CONTINUOUS_ON_SUB_FAN = prove
 (`!f g s. f uniformly_continuous_on_fan s /\ g uniformly_continuous_on_fan s
           ==> (\x. f(x) - g(x)) uniformly_continuous_on_fan s`,
  REWRITE_TAC[VECTOR_SUB] THEN
  SIMP_TAC[UNIFORMLY_CONTINUOUS_ON_NEG_FAN; UNIFORMLY_CONTINUOUS_ON_ADD_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Identity function is continuous in every sense.                           *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_ID_FAN = prove
 (`!net_fan a s. (\x. x) continuous_fan (at_fan a within_fan s)`,
  REWRITE_TAC[continuous_within_fan] THEN MESON_TAC[]);;

let CONTINUOUS_AT_ID_FAN = prove
 (`!net_fan s. (\x. x) continuous_fan (at_fan a)`,
  REWRITE_TAC[continuous_at_fan] THEN MESON_TAC[]);;

let CONTINUOUS_ON_ID_FAN = prove
 (`!s. (\x. x) continuous_on_fan s`,
  REWRITE_TAC[continuous_on_fan] THEN MESON_TAC[]);;

let UNIFORMLY_CONTINUOUS_ON_ID_FAN = prove
 (`!s. (\x. x) uniformly_continuous_on_fan s`,
  REWRITE_TAC[uniformly_continuous_on_fan] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of all kinds is preserved under composition.                   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_WITHIN_COMPOSE_FAN = prove
 (`!f g x s. f continuous_fan (at_fan x within_fan s) /\
             g continuous_fan (at_fan (f x) within_fan IMAGE f s)
             ==> (g o f) continuous_fan (at_fan x within_fan s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_within_fan; o_THM; IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_MESON_TAC[]);;

let CONTINUOUS_AT_COMPOSE_FAN = prove
 (`!f g x. f continuous_fan (at_fan x) /\ g continuous_fan (at_fan (f x))
           ==> (g o f) continuous_fan (at_fan x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV_FAN] THEN
  MESON_TAC[CONTINUOUS_WITHIN_COMPOSE_FAN; IN_IMAGE; CONTINUOUS_WITHIN_SUBSET_FAN;
            SUBSET_UNIV; IN_UNIV]);;

let CONTINUOUS_ON_COMPOSE_FAN = prove
 (`!f g s. f continuous_on_fan s /\ g continuous_on_fan (IMAGE f s)
           ==> (g o f) continuous_on_fan s`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN_FAN] THEN
  MESON_TAC[IN_IMAGE; CONTINUOUS_WITHIN_COMPOSE_FAN]);;


let UNIFORMLY_CONTINUOUS_ON_COMPOSE_FAN = prove
 (`!f g s. f uniformly_continuous_on_fan s /\
           g uniformly_continuous_on_fan (IMAGE f s)
           ==> (g o f) uniformly_continuous_on_fan s`,
(let lemma1 = prove
   (`(!y. ((?x. (y = f x) /\ P x) /\ Q y ==> R y)) <=>
     (!x. P x /\ Q (f x) ==> R (f x))`,
     MESON_TAC[]) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[uniformly_continuous_on_fan; o_THM; IN_IMAGE] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN REWRITE_TAC[lemma1] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN REWRITE_TAC[lemma1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `e:real` THEN ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]));;

(* ------------------------------------------------------------------------- *)
(* Continuity in terms of open preimages.                                    *)
(* ------------------------------------------------------------------------- *)
let CONTINUOUS_AT_OPEN_FAN = prove
 (`!f:real^M->real^N x.
     f continuous_fan (at_fan x) <=>
        !t. open_fan t /\ f(x) IN t
            ==> ?s. open_fan s /\ x IN s /\
                    !x'. x' IN s ==> f(x') IN t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_at_fan] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `t:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [open_def_fan] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^M->real^N) x`) THEN
    ASM_MESON_TAC[IN_BALL_FAN; DIST_SYM; OPEN_BALL_FAN; CENTRE_IN_BALL];
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ball_fan((f:real^M->real^N) x,e)`) THEN
    ASM_SIMP_TAC[OPEN_BALL_FAN; CENTRE_IN_BALL] THEN
    MESON_TAC[open_def_fan; IN_BALL_FAN; REAL_LT_TRANS; DIST_SYM]]);;


let CONTINUOUS_ON_OPEN_FAN = prove
 (`!f:real^M->real^N s.
      f continuous_on_fan s <=>
        !t. t open_in (IMAGE f s) ==> {x | x IN s /\ f(x) IN t} open_in s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_on_fan] THEN EQ_TAC THENL
   [REWRITE_TAC[open_in; SUBSET; IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIST_REFL]; ALL_TAC] THEN
    X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^M->real^N) x`) THEN
    ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    DISCH_TAC THEN X_GEN_TAC `x:real^M` THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o
      SPEC `ball_fan((f:real^M->real^N) x,e) INTER (IMAGE f s)`) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_OPEN_FAN; INTER_COMM; OPEN_BALL_FAN]; ALL_TAC] THEN
    REWRITE_TAC[open_in; SUBSET; IN_INTER; IN_ELIM_THM; IN_BALL_FAN; IN_IMAGE] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    ASM_MESON_TAC[DIST_REFL; DIST_SYM]]);;

(* ------------------------------------------------------------------------- *)
(* Similarly in terms of closed sets.                                        *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_CLOSED_FAN = prove
 (`!f:real^M->real^N s.
      f continuous_on_fan s <=>
        !t. t closed_in (IMAGE f s) ==> {x | x IN s /\ f(x) IN t} closed_in s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CONTINUOUS_ON_OPEN_FAN] THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `t:real^N->bool` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (f:real^M->real^N) s DIFF t`) THENL
   [REWRITE_TAC[closed_in]; REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ]] THEN
  MATCH_MP_TAC(TAUT`d /\ (b <=> e) ==> ((a ==> b) ==> c /\ a ==> d /\ e)`) THEN
  (CONJ_TAC THENL [SIMP_TAC[SUBSET; IN_ELIM_THM]; ALL_TAC] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[EXTENSION; IN_DIFF; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]));;

(* ------------------------------------------------------------------------- *)
(* The "global" cases.                                                       *)
(* ------------------------------------------------------------------------- *)

let CONTINOUS_OPEN_PREIMAGE_FAN = prove
 (`!f:real^M->real^N s.
        (!x. f continuous_fan (at_fan x)) /\ s SUBSET (IMAGE f UNIV) /\ open_fan s
        ==> open_fan {x | f(x) IN s}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:real^M->real^N`; `(:real^M)`]
	   CONTINUOUS_ON_OPEN_FAN) THEN
  ASM_SIMP_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON_FAN; IN_UNIV; GSYM OPEN_IN_FAN] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  UNDISCH_TAC `open_fan(s:real^N->bool)` THEN
  REWRITE_TAC[open_def_fan; open_in] THEN ASM_MESON_TAC[]);;

let OPEN_TRANSLATION_FAN = prove
 (`!s a:real^N. open_fan s ==> open_fan(IMAGE (\x. a + x) s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. x - a`; `s:real^N->bool`]
         CONTINOUS_OPEN_PREIMAGE_FAN) THEN
  ASM_SIMP_TAC[CONTINUOUS_SUB_FAN; CONTINUOUS_AT_ID_FAN; CONTINUOUS_CONST_FAN] THEN
  MATCH_MP_TAC(TAUT `a /\ b = c ==> (a ==> b) ==> c`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET]; AP_TERM_TAC THEN REWRITE_TAC[EXTENSION]] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
  ASM_MESON_TAC[VECTOR_ARITH `(a + x) - a = x:real^N`;
                VECTOR_ARITH `a + (x - a) = x:real^N`]);;

(* ------------------------------------------------------------------------- *)
(* Preservation of compactness and connectedness under continuous function.  *)
(* ------------------------------------------------------------------------- *)

let COMPACT_CONTINUOUS_IMAGE_FAN = prove
 (`!f:real^M->real^N s.
        f continuous_on_fan s /\ compact_fan s ==> compact_fan(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_on_fan; compact_fan] THEN
  STRIP_TAC THEN X_GEN_TAC `y:num->real^N` THEN
  REWRITE_TAC[IN_IMAGE; SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num->real^M` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num->real^M`) THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `r:num->num` THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(f:real^M->real^N) l` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY_FAN] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `l:real^M`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY_FAN]) THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[o_THM] THEN
  ASM_MESON_TAC[]);;

let CONNECTED_CONTINUOUS_IMAGE_FAN = prove
 (`!f:real^M->real^N s.
        f continuous_on_fan s /\ connected_fan s ==> connected_fan(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_ON_OPEN_FAN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[CONNECTED_CLOPEN_FAN; NOT_FORALL_THM; NOT_IMP; DE_MORGAN_THM] THEN
  REWRITE_TAC[closed_in] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `t:real^N->bool` th) THEN
    MP_TAC(SPEC `IMAGE (f:real^M->real^N) s DIFF t` th)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{x | x IN s /\ (f:real^M->real^N) x IN IMAGE f s DIFF t} =
                s DIFF {x | x IN s /\ f x IN t}`
  SUBST1_TAC THENL
   [UNDISCH_TAC `t SUBSET IMAGE (f:real^M->real^N) s` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF; IN_ELIM_THM; SUBSET] THEN
    MESON_TAC[];
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `{x | x IN s /\ (f:real^M->real^N) x IN t}` THEN
    ASM_REWRITE_TAC[] THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[IN_IMAGE; SUBSET; IN_ELIM_THM; NOT_IN_EMPTY; EXTENSION] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Continuity implies uniform continuity on a compact domain.                *)
(* ------------------------------------------------------------------------- *)

let COMPACT_UNIFORMLY_CONTINUOUS_FAN = prove
 (`!f:real^M->real^N s.
        f continuous_on_fan s /\ compact_fan s ==> f uniformly_continuous_on_fan s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[continuous_on_fan; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `d:real^M->real->real`) THEN
  REWRITE_TAC[uniformly_continuous_on_fan] THEN X_GEN_TAC `e:real` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP HEINE_BOREL_LEMMA_FAN) THEN
  DISCH_THEN(MP_TAC o SPEC
    `{b | ?x:real^M. x IN s /\ (b = ball_fan(x,d x (e / &2)))}`) THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_BALL_FAN] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[CENTRE_IN_BALL; REAL_HALF; OPEN_BALL_FAN]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `v:real^M` th) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CHOOSE_THEN MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `u:real^M` th) THEN MP_TAC(SPEC `v:real^M` th)) THEN
  ASM_REWRITE_TAC[DIST_REFL] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^M` (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST_ALL_TAC)) THEN
  REWRITE_TAC[IN_BALL_FAN] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC DIST_TRIANGLE_HALF_L THEN
  ASM_MESON_TAC[REAL_HALF]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of inverse function on compact domain.                         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_INVERSE_FAN = prove
 (`!f:real^M->real^N g s.
        f continuous_on_fan s /\ compact_fan s /\ (!x. x IN s ==> (g(f(x)) = x))
        ==> g continuous_on_fan (IMAGE f s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_CLOSED_FAN] THEN
  SUBGOAL_THEN `IMAGE g (IMAGE (f:real^M->real^N) s) = s` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[CLOSED_IN_CLOSED_FAN] THEN
  EXISTS_TAC `IMAGE (f:real^M->real^N) t` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN; BOUNDED_SUBSET_FAN; CLOSED_IN_SUBSET;
       CONTINUOUS_ON_SUBSET_FAN; CLOSED_IN_CLOSED_TRANS_FAN; COMPACT_CONTINUOUS_IMAGE_FAN];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
    ASM_MESON_TAC[CLOSED_IN_SUBSET; SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Topological properties of linear functions.                               *)
(* ------------------------------------------------------------------------- *)

let LINEAR_LIM_0_FAN = prove
 (`!f. linear f ==> (f --> vec 0) (at_fan (vec 0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIM_AT_FAN] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LINEAR_BOUNDED_POS) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `e / B` THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN REWRITE_TAC[dist; VECTOR_SUB_RZERO] THEN
  ASM_MESON_TAC[REAL_MUL_SYM; REAL_LET_TRANS; REAL_LT_RDIV_EQ]);;
(*error in old file*)
let LINEAR_CONTINUOUS_AT_FAN = prove
 (`!f:real^M->real^N a. linear f ==> f continuous_fan (at_fan a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x. (f:real^M->real^N) (a + x) - f(a)` LINEAR_LIM_0_FAN) THEN
  ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN SIMP_TAC[linear] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
   ALL_TAC  THEN
 REWRITE_TAC[GSYM LIM_NULL_FAN; CONTINUOUS_AT_FAN]THEN
  GEN_REWRITE_TAC RAND_CONV [LIM_AT_ZERO_FAN] THEN SIMP_TAC[]]);;


let LINEAR_CONTINUOUS_WITHIN_FAN = prove
 (`!f:real^M->real^N s a. linear f ==> f continuous_fan (at_fan x within_fan s)`,
  SIMP_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_WITHIN_FAN; LINEAR_CONTINUOUS_AT_FAN]);;


let LINEAR_CONTINUOUS_ON_FAN = prove
 (`!f:real^M->real^N s. linear f ==> f continuous_on_fan s`,
  MESON_TAC[LINEAR_CONTINUOUS_AT_FAN; CONTINUOUS_AT_IMP_CONTINUOUS_ON_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Topological stuff lifted from and dropped to R                            *)
(* ------------------------------------------------------------------------- *)

let OPEN_LIFT_FAN = prove
 (`!s. open_fan(IMAGE lift s) <=>
        !x. x IN s ==> ?e. &0 < e /\ !x'. abs(x' - x) < e ==> x' IN s`,
  REWRITE_TAC[open_def_fan; FORALL_LIFT; LIFT_IN_IMAGE_LIFT; DIST_LIFT]);;

let BOUNDED_LIFT_FAN = prove
 (`!s. bounded_fan(IMAGE lift s) <=>  ?a. !x. x IN s ==> abs(x) <= a`,
  REWRITE_TAC[bounded_fan; FORALL_LIFT; NORM_LIFT; LIFT_IN_IMAGE_LIFT]);;

let LIMPT_APPROACHABLE_LIFT_FAN = prove
 (`!x s. (lift x) limit_point_of_fan (IMAGE lift s) <=>
         !e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ abs(x' - x) < e`,
  REWRITE_TAC[LIMPT_APPROACHABLE_FAN; EXISTS_LIFT; LIFT_IN_IMAGE_LIFT;
              LIFT_EQ; DIST_LIFT]);;

let CLOSED_LIFT_FAN = prove
 (`!s. closed_fan (IMAGE lift s) <=>
        !x. (!e. &0 < e ==> ?x'. x' IN s /\ ~(x' = x) /\ abs(x' - x) < e)
            ==> x IN s`,
  GEN_TAC THEN REWRITE_TAC[CLOSED_LIMPT_FAN; LIMPT_APPROACHABLE_FAN] THEN
  ONCE_REWRITE_TAC[FORALL_LIFT] THEN
  REWRITE_TAC[LIMPT_APPROACHABLE_LIFT_FAN; LIFT_EQ; DIST_LIFT;
              EXISTS_LIFT; LIFT_IN_IMAGE_LIFT]);;

let CONTINUOUS_AT_LIFT_RANGE_FAN = prove
 (`!f x. (lift o f) continuous_fan (at_fan x) <=>
                !e. &0 < e
                    ==> ?d. &0 < d /\
                            (!x'. norm(x' - x) < d
                                  ==> abs(f x' - f x) < e)`,
  REWRITE_TAC[continuous_at_fan; o_THM; DIST_LIFT] THEN REWRITE_TAC[dist]);;

let CONTINUOUS_ON_LIFT_RANGE_FAN = prove
 (`!f s. (lift o f) continuous_on_fan s <=>
         !x. x IN s
             ==> !e. &0 < e
                     ==> ?d. &0 < d /\
                             (!x'. x' IN s /\ norm(x' - x) < d
                                   ==> abs(f x' - f x) < e)`,
  REWRITE_TAC[continuous_on_fan; o_THM; DIST_LIFT] THEN REWRITE_TAC[dist]);;

let CONTINUOUS_AT_LIFT_NORM_FAN = prove
 (`!x. (lift o norm) continuous_fan (at_fan x)`,
  REWRITE_TAC[CONTINUOUS_AT_LIFT_RANGE_FAN; NORM_LIFT] THEN
  MESON_TAC[REAL_ABS_SUB_NORM; REAL_LET_TRANS]);;

let CONTINUOUS_ON_LIFT_NORM_FAN = prove
 (`!s. (lift o norm) continuous_on_fan s`,
  REWRITE_TAC[CONTINUOUS_ON_LIFT_RANGE_FAN; NORM_LIFT] THEN
  MESON_TAC[REAL_ABS_SUB_NORM; REAL_LET_TRANS]);;

let CONTINUOUS_AT_LIFT_COMPONENT_FAN = prove
 (`!i a. 1 <= i /\ i <= dimindex(:N)
         ==> (\x:real^N. lift(x$i)) continuous_fan (at_fan a)`,
  SIMP_TAC[continuous_at_fan; DIST_LIFT; GSYM VECTOR_SUB_COMPONENT] THEN
  MESON_TAC[dist; REAL_LET_TRANS; COMPONENT_LE_NORM]);;

let CONTINUOUS_ON_LIFT_COMPONENT_FAN = prove
 (`!i s. 1 <= i /\ i <= dimindex(:N)
         ==> (\x:real^N. lift(x$i)) continuous_on_fan s`,
  SIMP_TAC[continuous_on_fan; DIST_LIFT; GSYM VECTOR_SUB_COMPONENT] THEN
  MESON_TAC[dist; REAL_LET_TRANS; COMPONENT_LE_NORM]);;

(* ------------------------------------------------------------------------- *)
(* Hence some handy theorems on distance, diameter etc. of/from a set.       *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_HAS_SUP_FAN = prove
 (`!s. bounded_fan(IMAGE lift s) /\ ~(s = {})
       ==> (!x. x IN s ==> x <= sup s) /\
           (!b. (!x. x IN s ==> x <= b) ==> sup s <= b)`,
  REWRITE_TAC[BOUNDED_LIFT_FAN; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[SUP; REAL_ARITH `abs(x) <= a ==> x <= a`]);;

let BOUNDED_HAS_INF_FAN = prove
 (`!s. bounded_fan(IMAGE lift s) /\ ~(s = {})
       ==> (!x. x IN s ==> inf s <= x) /\
           (!b. (!x. x IN s ==> b <= x) ==> b <= inf s)`,
  REWRITE_TAC[BOUNDED_LIFT_FAN; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[INF; REAL_ARITH `abs(x) <= a ==> --a <= x`]);;

let COMPACT_ATTAINS_SUP_FAN = prove
 (`!s. compact_fan (IMAGE lift s) /\ ~(s = {})
       ==> ?x. x IN s /\ !y. y IN s ==> y <= x`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` BOUNDED_HAS_SUP_FAN) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `sup s` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CLOSED_LIFT_FAN; REAL_ARITH `s <= s - e <=> ~(&0 < e)`;
                REAL_ARITH `x <= s /\ ~(x <= s - e) ==> abs(x - s) < e`]);;

let COMPACT_ATTAINS_INF_FAN = prove
 (`!s. compact_fan (IMAGE lift s) /\ ~(s = {})
       ==> ?x. x IN s /\ !y. y IN s ==> x <= y`,
  REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` BOUNDED_HAS_INF_FAN) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC `inf s` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[CLOSED_LIFT_FAN; REAL_ARITH `s + e <= s <=> ~(&0 < e)`;
                REAL_ARITH `s <= x /\ ~(s + e <= x) ==> abs(x - s) < e`]);;

let CONTINUOUS_ATTAINS_SUP_FAN = prove
 (`!f:real^N->real s.
        compact_fan s /\ ~(s = {}) /\ (lift o f) continuous_on_fan s
        ==> ?x. x IN s /\ !y. y IN s ==> f(y) <= f(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `IMAGE (f:real^N->real) s` COMPACT_ATTAINS_SUP_FAN) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; COMPACT_CONTINUOUS_IMAGE_FAN; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[IN_IMAGE]);;

let CONTINUOUS_ATTAINS_INF_FAN = prove
 (`!f:real^N->real s.
        compact_fan s /\ ~(s = {}) /\ (lift o f) continuous_on_fan s
        ==> ?x. x IN s /\ !y. y IN s ==> f(x) <= f(y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `IMAGE (f:real^N->real) s` COMPACT_ATTAINS_INF_FAN) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; COMPACT_CONTINUOUS_IMAGE_FAN; IMAGE_EQ_EMPTY] THEN
  MESON_TAC[IN_IMAGE]);;

let DISTANCE_ATTAINS_SUP_FAN = prove
 (`!s a. compact_fan s /\ ~(s = {})
         ==> ?x. x IN s /\ !y. y IN s ==> dist(a,y) <= dist(a,x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ATTAINS_SUP_FAN THEN
  ASM_REWRITE_TAC[CONTINUOUS_ON_LIFT_RANGE_FAN] THEN REWRITE_TAC[dist] THEN
  ASM_MESON_TAC[REAL_LET_TRANS; REAL_ABS_SUB_NORM; NORM_NEG;
                VECTOR_ARITH `(a - x) - (a - y) = --(x - y):real^N`]);;

(* ------------------------------------------------------------------------- *)
(* For *minimal* distance, we only need closure, not compactness.            *)
(* ------------------------------------------------------------------------- *)

let DISTANCE_ATTAINS_INF_FAN = prove
 (`!s a:real^N.
        closed_fan s /\ ~(s = {})
        ==> ?x. x IN s /\ !y. y IN s ==> dist(a,x) <= dist(a,y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real^N`) THEN
  MP_TAC(ISPECL [`\x:real^N. dist(a,x)`; `cball_fan(a:real^N,dist(b,a)) INTER s`]
                CONTINUOUS_ATTAINS_INF_FAN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN; CLOSED_INTER_FAN; BOUNDED_INTER_FAN;
                 BOUNDED_CBALL_FAN; CLOSED_CBALL_FAN; GSYM MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[dist; CONTINUOUS_ON_LIFT_RANGE_FAN; IN_INTER; IN_CBALL_FAN] THEN
    ASM_MESON_TAC[REAL_LET_TRANS; REAL_ABS_SUB_NORM; NORM_NEG; REAL_LE_REFL;
            NORM_SUB; VECTOR_ARITH `(a - x) - (a - y) = --(x - y):real^N`];
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[IN_INTER; IN_CBALL_FAN] THEN
    ASM_MESON_TAC[DIST_SYM; REAL_LE_TOTAL; REAL_LE_TRANS]]);;

(* ------------------------------------------------------------------------- *)
(* And so we have continuity of inverse.                                     *)
(* ------------------------------------------------------------------------- *)

let LIM_INV_FAN = prove
 (`!net_fan:(A)net_fan f l.
        ((lift o f) --> lift l) net_fan /\ ~(l = &0)
        ==> ((lift o inv o f) --> lift(inv l)) net_fan`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lim_fan] THEN
  ASM_CASES_TAC `trivial_limit_fan(net_fan:(A)net_fan)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[o_THM; DIST_LIFT] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `min (abs(l) / &2) ((l pow 2 * e) / &2)`) THEN
  REWRITE_TAC[REAL_LT_MIN] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_ABS_NZ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; GSYM REAL_ABS_NZ; REAL_POW_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:A` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `b:A` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  SIMP_TAC[REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REAL_ARITH
   `abs(x - l) * &2 < abs l ==> ~(x = &0)`)) THEN
  ASM_SIMP_TAC[REAL_SUB_INV; REAL_ABS_DIV; REAL_LT_LDIV_EQ;
               GSYM REAL_ABS_NZ; REAL_ENTIRE] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs(x - y) * &2 < b * c ==> c * b <= d * &2 ==> abs(y - x) < d`)) THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_LE_LMUL_EQ] THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_POW_2; REAL_MUL_ASSOC; GSYM REAL_ABS_NZ;
               REAL_LE_RMUL_EQ] THEN
  ASM_SIMP_TAC[REAL_ARITH `abs(x - y) * &2 < abs y ==> abs y <= &2 * abs x`]);;

let CONTINUOUS_INV_FAN = prove
 (`!net f. (lift o f) continuous_fan net_fan /\ ~(f(netlimit_fan net_fan) = &0)
           ==> (lift o inv o f) continuous_fan net_fan`,
  REWRITE_TAC[continuous_fan; LIM_INV_FAN; o_THM]);;

let CONTINUOUS_AT_WITHIN_INV_FAN = prove
 (`!f s a:real^N.
        (lift o f) continuous_fan (at_fan a within_fan s) /\ ~(f a = &0)
        ==> (lift o inv o f) continuous_fan (at_fan a within_fan s)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `trivial_limit_fan (at_fan (a:real^N) within_fan s)` THENL
   [ASM_REWRITE_TAC[continuous_fan; lim_fan];
    ASM_SIMP_TAC[NETLIMIT_WITHIN_FAN; CONTINUOUS_INV_FAN]]);;

let CONTINUOUS_AT_INV_FAN = prove
 (`!f a. (lift o f) continuous_fan at_fan a /\ ~(f a = &0)
         ==> (lift o inv o f) continuous_fan at_fan a`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV_FAN] THEN
  REWRITE_TAC[CONTINUOUS_AT_WITHIN_INV_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Preservation properties for pasted sets.                                  *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_PASTECART_FAN = prove
 (`!s:real^M->bool t:real^N->bool.
     bounded_fan s /\ bounded_fan t ==> bounded_fan {pastecart x y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bounded_fan; IN_ELIM_THM] THEN
  ASM_MESON_TAC[NORM_PASTECART; REAL_LE_ADD2; REAL_LE_TRANS]);;

let CLOSED_PASTECART_FAN = prove
 (`!s:real^M->bool t:real^N->bool.
     closed_fan s /\ closed_fan t ==> closed_fan {pastecart x y | x IN s /\ y IN t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_SEQUENTIAL_LIMITS_FAN] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY_FAN; IN_ELIM_THM; dist] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`z:num->real^(M,N)finite_sum`; `l:real^(M,N)finite_sum`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num->real^M`; `y:num->real^N`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`fstcart(l:real^(M,N)finite_sum)`; `sndcart(l:real^(M,N)finite_sum)`] THEN
  REWRITE_TAC[PASTECART_FST_SND] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `x:num->real^M`; EXISTS_TAC `y:num->real^N`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < a ==> x < a`) THEN
  MESON_TAC[NORM_FSTCART; FSTCART_SUB; FSTCART_PASTECART;
            NORM_SNDCART; SNDCART_SUB; SNDCART_PASTECART]);;

let COMPACT_PASTECART_FAN = prove
 (`!s:real^M->bool t:real^N->bool.
     compact_fan s /\ compact_fan t ==> compact_fan {pastecart x y | x IN s /\ y IN t}`,
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED_FAN; BOUNDED_PASTECART_FAN; CLOSED_PASTECART_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Hence some useful properties follow quite easily.                         *)
(* ------------------------------------------------------------------------- *)

let COMPACT_MULTIPLES_FAN = prove
 (`!s:real^N->bool c. compact_fan s ==> compact_fan (IMAGE (\x. c % x) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE_FAN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON_FAN THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT_FAN THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let COMPACT_NEGATIONS_FAN = prove
 (`!s:real^N->bool. compact_fan s ==> compact_fan (IMAGE (--) s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE_FAN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON_FAN THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT_FAN THEN
  REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let COMPACT_SUMS_FAN = prove
 (`!s:real^N->bool t.
        compact_fan s /\ compact_fan t ==> compact_fan {x + y | x IN s /\ y IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x + y | x IN s /\ y IN t} =
                IMAGE (\z. fstcart z + sndcart z :real^N)
                      {pastecart x y | x IN s /\ y IN t}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FSTCART_PASTECART; SNDCART_PASTECART; PASTECART_FST_SND];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE_FAN THEN
  ASM_SIMP_TAC[COMPACT_PASTECART_FAN] THEN
  MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON_FAN THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT_FAN THEN
  REWRITE_TAC[linear; FSTCART_ADD; FSTCART_CMUL; SNDCART_ADD;
              SNDCART_CMUL] THEN
  CONJ_TAC THEN VECTOR_ARITH_TAC);;

let COMPACT_DIFFERENCES_FAN = prove
 (`!s:real^N->bool t.
        compact_fan s /\ compact_fan t ==> compact_fan {x - y | x IN s /\ y IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x - y | x:real^N IN s /\ y IN t} =
                {x + y | x IN s /\ y IN (IMAGE (--) t)}`
    (fun th -> ASM_SIMP_TAC[th; COMPACT_SUMS_FAN; COMPACT_NEGATIONS_FAN]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `(x:real^N = --y) <=> (y = --x)`] THEN
  SIMP_TAC[VECTOR_SUB; GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  MESON_TAC[VECTOR_NEG_NEG]);;

let COMPACT_TRANSLATION_FAN = prove
 (`!s a:real^N. compact_fan s ==> compact_fan (IMAGE (\x. a + x) s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{a:real^N}`; `s:real^N->bool`] COMPACT_SUMS_FAN) THEN
  ASM_REWRITE_TAC[COMPACT_SING_FAN] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; IN_IMAGE] THEN MESON_TAC[]);;

let COMPACT_AFFINITY_FAN = prove
 (`!s a:real^N c.
        compact_fan s ==> compact_fan (IMAGE (\x. a + c % x) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. a + c % x) = (\x. a + x) o (\x. c % x)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  ASM_SIMP_TAC[IMAGE_o; COMPACT_TRANSLATION_FAN; COMPACT_MULTIPLES_FAN]);;

(* ------------------------------------------------------------------------- *)
(* Hence we get the following.                                               *)
(* ------------------------------------------------------------------------- *)

let COMPACT_SUP_MAXDISTANCE_FAN = prove
 (`!s:real^N->bool.
        compact_fan s /\ ~(s = {})
        ==> ?x y. x IN s /\ y IN s /\
                  !u v. u IN s /\ v IN s ==> norm(u - v) <= norm(x - y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{x - y:real^N | x IN s /\ y IN s}`; `vec 0:real^N`]
                DISTANCE_ATTAINS_SUP_FAN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_DIFFERENCES_FAN] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY];
    REWRITE_TAC[IN_ELIM_THM; dist; VECTOR_SUB_RZERO; VECTOR_SUB_LZERO;
                NORM_NEG] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* We can state this in terms of diameter of a set.                          *)
(* ------------------------------------------------------------------------- *)

let diameter_fan = new_definition
  `diameter_fan s =
        if s = {} then &0
        else sup {norm(x - y) | x IN s /\ y IN s}`;;

let DIAMETER_BOUNDED_FAN = prove
 (`!s. bounded_fan s
       ==> (!x:real^N y. x IN s /\ y IN s ==> norm(x - y) <= diameter_fan s) /\
           (!d. &0 <= d /\ d < diameter_fan s
                ==> ?x y. x IN s /\ y IN s /\ norm(x - y) > d)`,
  GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[diameter_fan; NOT_IN_EMPTY; REAL_LET_ANTISYM] THEN
  MP_TAC(SPEC `{norm(x - y:real^N) | x IN s /\ y IN s}` SUP) THEN
  ABBREV_TAC `b = sup {norm(x - y:real^N) | x IN s /\ y IN s}` THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[NOT_IN_EMPTY; real_gt] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC];
    MESON_TAC[REAL_NOT_LE]] THEN
  SIMP_TAC[VECTOR_SUB; LEFT_IMP_EXISTS_THM] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded_fan]) THEN
  MESON_TAC[REAL_ARITH `x <= y + z /\ y <= b /\ z<= b ==> x <= b + b`;
            NORM_TRIANGLE; NORM_NEG]);;

let DIAMETER_BOUNDED_BOUND_FAN = prove
 (`!s x y. bounded_fan s /\ x IN s /\ y IN s ==> norm(x - y) <= diameter_fan s`,
  MESON_TAC[DIAMETER_BOUNDED_FAN]);;

let DIAMETER_COMPACT_ATTAINED_FAN = prove
 (`!s:real^N->bool.
        compact_fan s /\ ~(s = {})
        ==> ?x y. x IN s /\ y IN s /\ (norm(x - y) = diameter_fan s)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_SUP_MAXDISTANCE_FAN) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `s:real^N->bool` DIAMETER_BOUNDED_FAN) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPACT_EQ_BOUNDED_CLOSED_FAN]) THEN
  ASM_REWRITE_TAC[real_gt] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  ASM_MESON_TAC[NORM_POS_LE; REAL_NOT_LT]);;

(* ------------------------------------------------------------------------- *)
(* Related results with closure as the conclusion.                           *)
(* ------------------------------------------------------------------------- *)

let CLOSED_MULTIPLES_FAN = prove
 (`!s:real^N->bool c. closed_fan s ==> closed_fan (IMAGE (\x. c % x) s)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s :real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CLOSED_EMPTY_FAN; IMAGE_CLAUSES] THEN
  ASM_CASES_TAC `c = &0` THENL
   [SUBGOAL_THEN `IMAGE (\x:real^N. c % x) s = {(vec 0)}`
     (fun th -> REWRITE_TAC[th; CLOSED_SING_FAN]) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SING; VECTOR_MUL_LZERO] THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSED_SEQUENTIAL_LIMITS_FAN; IN_IMAGE; SKOLEM_THM] THEN
  STRIP_TAC THEN X_GEN_TAC `x:num->real^N` THEN X_GEN_TAC `l:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num->real^N` MP_TAC) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `inv(c) % l :real^N` THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `\n:num. inv(c) % x n:real^N` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID];
    MATCH_MP_TAC LIM_CMUL_FAN THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[SYM(SPEC_ALL th)]) THEN
    ASM_REWRITE_TAC[ETA_AX]]);;

let CLOSED_NEGATIONS_FAN = prove
 (`!s:real^N->bool. closed_fan s ==> closed_fan (IMAGE (--) s)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `IMAGE (--) s = IMAGE (\x:real^N. --(&1) % x) s`
  SUBST1_TAC THEN SIMP_TAC[CLOSED_MULTIPLES_FAN] THEN
  REWRITE_TAC[VECTOR_ARITH `--(&1) % x = --x`] THEN REWRITE_TAC[ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* A cute way of denoting open and closed intervals using overloading.       *)
(* ------------------------------------------------------------------------- *)

let open_interval_fan = new_definition
  `open_interval_fan(a:real^N,b:real^N) =
        {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                        ==> a$i < x$i /\ x$i < b$i}`;;

let closed_interval_fan = new_definition
  `closed_interval_fan(l:(real^N#real^N)list) =
         {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                         ==> FST(HD l)$i <= x$i /\ x$i <= SND(HD l)$i}`;;

make_overloadable "interval_fan" `:A`;;

overload_interface("interval_fan",`open_interval_fan`);;
overload_interface("interval_fan",`closed_interval_fan`);;

let interval_fan = prove
 (`(interval_fan (a,b) = {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                     ==> a$i < x$i /\ x$i < b$i}) /\
   (interval_fan [a,b] = {x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                     ==> a$i <= x$i /\ x$i <= b$i})`,
  REWRITE_TAC[open_interval_fan; closed_interval_fan; HD; FST; SND]);;

let IN_INTERVAL_FAN = prove
 (`(!x:real^N.
        x IN interval_fan (a,b) <=>
                !i. 1 <= i /\ i <= dimindex(:N)
                    ==> a$i < x$i /\ x$i < b$i) /\
   (!x:real^N.
        x IN interval_fan [a,b] <=>
                !i. 1 <= i /\ i <= dimindex(:N)
                    ==> a$i <= x$i /\ x$i <= b$i)`,
  REWRITE_TAC[interval_fan; IN_ELIM_THM]);;


(* ------------------------------------------------------------------------- *)
(* Some stuff for half-infinite intervals too; maybe I need a notation?      *)
(* ------------------------------------------------------------------------- *)

let CLOSED_INTERVAL_LEFT_FAN = prove
 (`!b:real^N.
     closed_fan
        {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> x$i <= b$i}`,
  REWRITE_TAC[CLOSED_LIMPT_FAN; LIMPT_APPROACHABLE_FAN; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(x:real^N)$i - (b:real^N)$i`) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[dist; REAL_NOT_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((z - x :real^N)$i)` THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_ARITH `z <= b /\ b < x ==> x - b <= abs(z - x)`]);;

let CLOSED_INTERVAL_RIGHT_FAN = prove
 (`!a:real^N.
     closed_fan
        {x:real^N | !i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= x$i}`,
  REWRITE_TAC[CLOSED_LIMPT_FAN; LIMPT_APPROACHABLE_FAN; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a:real^N)$i - (x:real^N)$i`) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[dist; REAL_NOT_LT] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((z - x :real^N)$i)` THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
  ASM_SIMP_TAC[REAL_ARITH `x < a /\ a <= z ==> a - x <= abs(z - x)`]);;

(* ------------------------------------------------------------------------- *)
(* Closure of halfspaces and hyperplanes.                                    *)
(* ------------------------------------------------------------------------- *)

let LIM_LIFT_DOT_FAN = prove
 (`!f:real^M->real^N a.
        (f --> l) net_fan ==> ((lift o (\y. a dot f(y))) --> lift(a dot l)) net_fan`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = vec 0:real^N` THENL
   [ASM_REWRITE_TAC[DOT_LZERO; LIFT_NUM; o_DEF; LIM_CONST_FAN]; ALL_TAC] THEN
  REWRITE_TAC[lim_fan] THEN MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / norm(a:real^N)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; NORM_POS_LT; REAL_LT_RDIV_EQ] THEN
  REWRITE_TAC[dist; o_THM; GSYM LIFT_SUB; GSYM DOT_RSUB; NORM_LIFT] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN
  MESON_TAC[NORM_CAUCHY_SCHWARZ_ABS; REAL_MUL_SYM; REAL_LET_TRANS]);;

let CONTINUOUS_AT_LIFT_DOT_FAN = prove
 (`!a:real^N x. (lift o (\y. a dot y)) continuous_fan at_fan x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_AT_FAN; o_THM] THEN
  MATCH_MP_TAC LIM_LIFT_DOT_FAN THEN REWRITE_TAC[LIM_AT_FAN] THEN MESON_TAC[]);;

let CONTINUOUS_ON_LIFT_DOT_FAN = prove
 (`!s x. (lift o (\y. a dot y)) continuous_on_fan s`,
  SIMP_TAC[CONTINUOUS_AT_IMP_CONTINUOUS_ON_FAN; CONTINUOUS_AT_LIFT_DOT_FAN]);;

let CLOSED_HALFSPACE_LE_FAN = prove
 (`!a:real^N b. closed_fan {x | a dot x <= b}`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`(:real^N)`; `a:real^N`] CONTINUOUS_ON_LIFT_DOT_FAN) THEN
  REWRITE_TAC[CONTINUOUS_ON_CLOSED_FAN; GSYM CLOSED_IN_FAN] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE lift {r | ?x:real^N. (a dot x = r) /\ r <= b}`) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_UNIV] THEN
    REWRITE_TAC[o_DEF] THEN MESON_TAC[LIFT_DROP]] THEN
  REWRITE_TAC[CLOSED_IN_CLOSED_FAN] THEN
  EXISTS_TAC `{x | !i. 1 <= i /\ i <= dimindex(:1)
                       ==> (x:real^1)$i <= (lift b)$i}` THEN
  REWRITE_TAC[CLOSED_INTERVAL_LEFT_FAN] THEN
  SIMP_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_ELIM_THM; IN_INTER; IN_INTERVAL_FAN;
    VEC_COMPONENT; DIMINDEX_1; LAMBDA_BETA; o_THM] THEN
  SIMP_TAC[ARITH_RULE `1 <= i /\ i <= 1 <=> (i = 1)`] THEN
  REWRITE_TAC[GSYM drop; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  MESON_TAC[LIFT_DROP]);;

let CLOSED_HALFSPACE_GE_FAN = prove
 (`!a:real^N b. closed_fan {x | a dot x >= b}`,
  REWRITE_TAC[REAL_ARITH `a >= b <=> --a <= --b`] THEN
  REWRITE_TAC[GSYM DOT_LNEG; CLOSED_HALFSPACE_LE_FAN]);;

let CLOSED_HYPERPLANE_FAN = prove
 (`!a b. closed_fan {x | a dot x = b}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
  REWRITE_TAC[REAL_ARITH `b <= a dot x <=> a dot x >= b`] THEN
  REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  SIMP_TAC[CLOSED_INTER_FAN; CLOSED_HALFSPACE_LE_FAN; CLOSED_HALFSPACE_GE_FAN]);;




