(* Formal Spec of Blueprint Chapter  on Collection of Problems in Geometry *)

needs "Examples/transc.ml";;
needs "definitions_kepler.ml";;

prioritize_real();;

(* NGUYEN DUC PHUONG *)
(* Definition of Cayley – Menger square cm3 *)
let cm3_ups_x = new_definition `!(v1:real^3) (v2:real^3) (v3:real^3).
   cm3_ups_x v1 v2 v3 = 
  (((v2 - v1)$2 * (v3 - v1)$3 ) - ((v2 - v1)$3 * (v3 - v1)$2)) pow 2 +
  (((v2 - v1)$3 * (v3 - v1)$1 ) - ((v2 - v1)$1 * (v3 - v1)$3)) pow 2 +
  (((v2 - v1)$1 * (v3 - v1)$2 ) - ((v2 - v1)$2 * (v3 - v1)$1)) pow 2 `;;

(* Nguyen Tuyen Hoang, Nguyen Duc Phuong *)

(* The polynomial ups can be expressed as a Cayley- Menger square *)  

let lemma_cm3 = prove (`!(x:real^3) y. 
(x-y)$1 = x$1 - y$1 /\ (x-y)$2 = x$2 - y$2 /\ (x-y)$3 = x$3 - y$3`, 

(REPEAT GEN_TAC) THEN (REPEAT CONJ_TAC) THENL 
[(MESON_TAC[VECTOR_SUB_COMPONENT;DIMINDEX_3;ARITH_RULE `1 <= 1 /\ 1 <= 3`]);
(MESON_TAC[VECTOR_SUB_COMPONENT;DIMINDEX_3;ARITH_RULE `1 <= 2 /\ 2 <= 3`]);
(MESON_TAC[VECTOR_SUB_COMPONENT;DIMINDEX_3;ARITH_RULE `1 <= 3 /\ 3 <= 3`])]);;

let lemma7 = prove ( `! (v1 : real ^3)(v2: real^3)(v3:real^3).
  cm3_ups_x v1 v2 v3 = 
  ups_x (norm (v1 -v2) pow 2) (norm (v2 -v3) pow 2) (norm (v3 -v1) pow 2) / &4`,

 (REPEAT GEN_TAC) THEN
 (REWRITE_TAC[cm3_ups_x; ups_x]) THEN
 (REWRITE_TAC[GSYM DOT_SQUARE_NORM;DOT_3;REAL_POW_2]) THEN
 (REWRITE_TAC[lemma_cm3]) THEN
  REAL_ARITH_TAC );;

let pow_g = prove ( `! (x:real). &0 <= x pow 2`,
  GEN_TAC THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE]);;

let lemma8 = prove ( `! (v1:real^3)(v2:real^3)(v3:real^3). 
&0 <= ups_x (norm (v1 - v2) pow 2)(norm (v2 - v3) pow 2)(norm (v3 - v1) pow 2)`,
 (REPEAT GEN_TAC)
THEN (MATCH_MP_TAC (REAL_ARITH `&0 <= a/ &4 ==> &0 <= a `))
THEN (REWRITE_TAC[GSYM lemma7])
THEN (REWRITE_TAC[cm3_ups_x])

THEN (ABBREV_TAC `(a:real) = (((v2:real^3) - v1)$2 * (v3 - v1)$3 - (v2 - v1)$3 * (v3 - v1)$2) pow 2`)
THEN (FIRST_X_ASSUM ((LABEL_TAC "1") o GSYM))
THEN (ABBREV_TAC `(b:real) = (((v2:real^3) - v1)$3 * (v3 - v1)$1 - (v2 - v1)$1 * (v3 - v1)$3) pow 2`)
THEN (FIRST_X_ASSUM((LABEL_TAC "2") o GSYM))
THEN (ABBREV_TAC `(c:real) = (((v2:real^3) - v1)$1 * (v3 - v1)$2 - (v2 - v1)$2 * (v3 - v1)$1) pow 2`)
THEN (FIRST_X_ASSUM((LABEL_TAC "3") o GSYM))

THEN (MATCH_MP_TAC (SPEC_ALL REAL_LE_ADD))
THEN CONJ_TAC
THEN (ASM_REWRITE_TAC[pow_g])
THEN (MATCH_MP_TAC (SPEC_ALL REAL_LE_ADD))
THEN CONJ_TAC
THEN (ASM_REWRITE_TAC[pow_g]));;

(* VUONG ANH QUYEN *)
let line_exists = prove
( ` ? l:real^N ->real^N ->(real^N->bool). ! (u:real^N) v. ~(u = v) 
  ==> (line (l u v))/\(u IN (l u v))/\(v IN (l u v))/\
 (! d:real^N->bool. (line d)/\ (u IN d)/\ (v IN d) ==> d = l u v)`, 

let pr1 = prove 
( ` ! (t:real) t'. ~(t = t') ==> 
( (&1 - t') / (t - t') * t + (&1 - (&1 - t') / (t - t')) * t' = &1) /\
 ((&1 - t') / (t - t') * (&1 - t) + (&1 - (&1 - t') / (t - t')) * (&1 - t') = &0)`,
REPEAT GEN_TAC THEN ABBREV_TAC ` m:real = (&1 - t') / (t - t')` THEN
FIRST_X_ASSUM(LABEL_TAC "m" o GSYM) THEN 
ONCE_REWRITE_TAC[REAL_ARITH ` ~(t:real = t') <=> ~(t - t' = &0)`] THEN
DISCH_TAC THEN FIRST_X_ASSUM (MP_TAC o (MATCH_MP REAL_DIV_RMUL)) THEN
DISCH_TAC THEN CONJ_TAC THENL
[REWRITE_TAC[ARITH_RULE `m * t + (&1 - m) * t' = m * (t - t') + t'`];
 REWRITE_TAC[ARITH_RULE `m * (&1 - t) + (&1 - m) * (&1 - t') = &1 - t' - m * (t - t')`]] THEN
ASM_REWRITE_TAC[] THEN ARITH_TAC) in

let pr2 = prove
(`! (a:real^N) b u v. (a IN aff {u,v})/\(b IN aff {u,v}) ==>(aff {a,b} SUBSET aff {u,v})`,
REPEAT GEN_TAC THEN 
DISCH_THEN (MP_TAC o (MATCH_MP (SET_RULE `! (a:A) b (M:A->bool). a IN M /\ b IN M ==> {a,b} SUBSET M`))) THEN
DISCH_THEN (MP_TAC o (MATCH_MP aff_SUBSET)) THEN
REWRITE_TAC[MATCH_MP aff_affine (SPEC_ALL affine_aff)] ) in

let pr3 = prove
(` ! (u:real^N) v a b. ~(u = v)/\ (u IN aff {a,b}) /\ (v IN aff {a,b}) ==> (a IN aff {u,v})`,
REPEAT GEN_TAC THEN REWRITE_TAC[aff_2;IN_ELIM_THM] THEN STRIP_TAC THEN
ASM_CASES_TAC ` t:real = t'` THENL
[ ASM_MESON_TAC[]; EXISTS_TAC ` (&1 - t') / (t - t')` THEN
  ASM_REWRITE_TAC[VECTOR_ADD_LDISTRIB;VECTOR_MUL_ASSOC ] THEN
  ONCE_REWRITE_TAC[ VECTOR_ARITH ` ( (m:real^N) + n) + ( p + q) = ( m + p) +( n + q)`] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB ] THEN FIRST_X_ASSUM(MP_TAC o (MATCH_MP pr1)) THEN
  MESON_TAC[ VECTOR_ARITH ` a:real^N = &1 % a + &0 % b`] ]) in

let pr4 = prove
( `! (a:real^N) b u v. ~( u = v )/\ ( u IN aff {a,b})/\ (v IN aff {a,b}) ==> (aff {u,v} = aff {a,b})`,
REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN DISCH_TAC THEN CONJ_TAC THENL
[ ASM_MESON_TAC[pr2];MATCH_MP_TAC(pr2)] THEN CONJ_TAC THENL
[ ASM_MESON_TAC[pr3];UNDISCH_TAC `~(u:real^N = v) /\ u IN aff {a, b} /\ v IN aff {a, b}` THEN 
ONCE_REWRITE_TAC[SET_RULE `{a,b} = {b,a}`] THEN MESON_TAC[pr3] ] ) in

ABBREV_TAC ` l = (\ (u:real^N) v. aff {u,v})` THEN FIRST_X_ASSUM(LABEL_TAC "l" o GSYM) THEN
EXISTS_TAC `l:real^N ->real^N->(real^N->bool)`  THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN 
ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
[ ASM_MESON_TAC[line]; MP_TAC(SPEC ` ({u,v} :real^N->bool)` SUBSET_aff) THEN SET_TAC[];
  MP_TAC(SPEC ` ({u,v} :real^N->bool)` SUBSET_aff) THEN SET_TAC[];GEN_TAC THEN REWRITE_TAC[line] THEN
 STRIP_TAC THEN ASM_MESON_TAC[pr4]]);; 

let line_match_def = new_specification ["line_match"] line_exists;;

let line_unique = prove
(`! u:real^N v. ~(u = v) ==> (?! (d:real^N->bool). (line d)/\(u IN d)/\(v IN d))`,
MESON_TAC[line_match_def]);;

let lemma4 = prove
(`! u:real^N v. ~(u=v) ==> aff {u,v} = line_match u v`,
REPEAT GEN_TAC THEN DISCH_TAC THEN
FIRST_ASSUM(MP_TAC o (MATCH_MP line_match_def)) THEN STRIP_TAC THEN
FIRST_ASSUM(MATCH_MP_TAC o (SPEC ` (aff {u, v}):real^N->bool`)) THEN
REPEAT CONJ_TAC THENL
  [ ASM_MESON_TAC[line]; MP_TAC(SPEC ` ({u,v} :real^N->bool)` SUBSET_aff) THEN SET_TAC[];
  MP_TAC(SPEC ` ({u,v} :real^N->bool)` SUBSET_aff) THEN SET_TAC[]]);;

