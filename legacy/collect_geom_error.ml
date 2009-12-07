(* Moved by Thales from collect_geom.ml on Nov 11, 2008 because of
   syntax and proof errors. *)

(* VUONG ANH QUYEN *)
let line_exists = prove
( ` ? l:real^N ->real^N ->(real^N->bool). ! (u:real^N) v. ~(u = v) 
  ==> (line (l u v))/\(u IN (l u v))/\(v IN (l u v))/\
 (! d:real^N->bool. (line d)/\ (u IN d)/\ (v IN d) ==> d = l u v)`

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


