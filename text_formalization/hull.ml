(*VUONG ANH QUYEN *)
(* DEFINITIONS OF AFFINE HULL.                                          *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
(* Two ways to define affine set & affine hull.                        *)
(* -------------------------------------------------------------------- *)

(* Define as in convex.ml                                               *)
(* -------------------------------------------------------------------- *)

(* Define using affine combination                                      *)
(* -------------------------------------------------------------------- *)

let affine_comb = new_definition `!(s:real^N->bool). affine_comb s = ! (n:num) (t:num->real) (v:num->real^N).
  ( sum (1..n) (\i. t i) = &1)/\(!i. ((1..n) i) ==>(s (v i)))
  ==> (s (vsum (1..n) (\i. (t i) % (v i))))`;;

let aff_comb = new_definition `! (S:real^N -> bool) (w:real^N). aff_comb S w =(
  ? (n:num) (t:num->real) (v:num->real^N). 
  (  sum (1..n) (\i. t i) = &1 ) /\ 
  (w = vsum (1..n) (\i. (t i) % (v i)))/\ (!i. ((1..n) i) ==> (S (v i))) )`;;

(* Some simple properties of affine, aff, affine_comb, aff_comb, hull   *)
(* -------------------------------------------------------------------- *)

let affine_INTERS = prove 
  ( `(!s. s IN f ==> affine s) ==> affine(INTERS f)`,
  (REWRITE_TAC[affine;INTERS;IN;IN_ELIM_THM] THEN MESON_TAC[]));;

let affine_aff = prove 
  ( `!(s:real^N->bool). affine (aff s)`,
  (GEN_TAC THEN REWRITE_TAC[aff] THEN MESON_TAC[affine_INTERS;P_HULL]));;

let aff_affine = prove
  ( `!s. affine S ==> aff S = S`,
  (SIMP_TAC[HULL_EQ;aff;affine_INTERS]));;

let SUBSET_hull = prove  
  (`! s P. s SUBSET (P hull s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET;hull;IN_INTERS] THEN SET_TAC[]);;

let SUBSET_aff = prove 
  ( `!(S:real^N->bool). S SUBSET aff S`, MESON_TAC [SUBSET;aff;SUBSET_hull]);;

let SUBSET_affcomb = prove
(`!(S:real^N->bool). S SUBSET (aff_comb S)`,
GEN_TAC THEN REWRITE_TAC[SUBSET;IN;aff_comb] THEN GEN_TAC THEN STRIP_TAC THEN
EXISTS_TAC `1` THEN EXISTS_TAC `(\(i:num). &1)` THEN EXISTS_TAC `(\(i:num). x:real^N)` THEN 
ASM_SIMP_TAC[SUM_SING_NUMSEG;NUMSEG_SING;VSUM_SING;VECTOR_MUL_LID;IN;IN_SING]);;

let aff_SUBSET = prove
  (`!A B. A SUBSET B ==> aff A SUBSET aff B`,
  (REPEAT GEN_TAC THEN 
   REWRITE_TAC [aff; hull;SUBSET;IN;INTERS;IN_INTERS;IN_ELIM_THM] THEN MESON_TAC[]));;

let INTERS_SUBSET = prove
(`!(S:(A->bool)->bool) (u:A->bool). u IN S ==> (INTERS S) SUBSET u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET;IN_INTERS] THEN MESON_TAC[]);;

let hull_SUBSET = prove
( `!(P:(A->bool)->bool) (S:A->bool) (u:A->bool). (S SUBSET u)/\(P u) ==> (P hull S) SUBSET u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[hull] THEN MATCH_MP_TAC (INTERS_SUBSET) THEN
  ASM_REWRITE_TAC[IN;IN_ELIM_THM]);;

(* Some lemmas need using                                          *)
(* --------------------------------------------------------------- *)
let VSUM_2 = prove
  ( `! (v:num->real^N). vsum (1..2)  v  = (v 1) + (v 2)`,
  GEN_TAC THEN REWRITE_TAC[vsum; SUM_2] THEN VECTOR_ARITH_TAC);;

let REAL_OF_NUM_NOT_EQ = prove
   ( `!n m. ~(m = n) <=> ~(&m = &n)`, MESON_TAC[REAL_OF_NUM_EQ]);;

let VMUL_CASES = prove
  (`!(P:A->bool) (t:A->real) (t':A->real) (v:A->real^N) (v':A->real^N). (if P i then t i else t' i) % (if P i then v i else v' i) = (if P i then ( t i % v i) else (t' i % v' i))`,
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* Relation between affine and affine_comb                         *)
(* --------------------------------------------------------------- *)

let affcomb_imp_aff = prove
  ( `!(S:real^N->bool). affine_comb S ==> affine S`,
    GEN_TAC THEN REWRITE_TAC[affine;affine_comb] THEN STRIP_TAC THEN REPEAT GEN_TAC THEN 
    FIRST_X_ASSUM (MP_TAC o SPECL [`2`;`(\i. if (i=1) then t else (&1-t))`;`(\i. if (i=1) then (u:real^N) else (v:real^N))`])
    THEN SIMP_TAC[SUM_2;VSUM_2;ARITH_RULE `~(1=2)/\(!t. t + (&1 - t) = &1)`] THEN MESON_TAC[]);;

let comb_trans = prove (
  `! (n:num) (t:num->real) (v:num->real^N). 
~(n=0)/\(sum (1..n+1) (\i. t i) = &1)==> 
(vsum (1..n+1) (\i. (t i) % (v i)) = vsum (1..n) (\i. (&1 / &n) % ((&n * (t i)) % (v i) + (&1 - &n * (t i)) % (v (n+1)))))`,
  REPEAT GEN_TAC THEN 
  REWRITE_TAC[ REAL_OF_NUM_NOT_EQ;VSUM_CMUL_NUMSEG; VECTOR_ADD_LDISTRIB;VSUM_ADD_NUMSEG] THEN
  REWRITE_TAC[GSYM VSUM_CMUL_NUMSEG; VECTOR_MUL_ASSOC;REAL_MUL_ASSOC;REAL_SUB_LDISTRIB] THEN
  STRIP_TAC THEN (FIRST_ASSUM (MP_TAC o MATCH_MP REAL_DIV_RMUL)) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_LID;REAL_MUL_RID] THEN
  REWRITE_TAC[MATCH_MP VSUM_CLAUSES_RIGHT (ARITH_RULE ` (0 < (n+1))/\(1 <= (n+1))`)] THEN
  ASM_REWRITE_TAC[ ARITH_RULE `! (n:num). (n + 1)-1 = n`;VSUM_RMUL] THEN
  ASM_REWRITE_TAC[SUM_CONST_NUMSEG;SUM_SUB_NUMSEG;REAL_MUL_SYM; ARITH_RULE `(n+1) -1 = n`] THEN
  (UNDISCH_TAC `sum (1..n + 1) (\i. t i) = &1`) THEN
  ASM_REWRITE_TAC [MATCH_MP SUM_CLAUSES_RIGHT (ARITH_RULE ` (0 < (n+1))/\(1 <= (n+1))`);ARITH_RULE `(n+1) - 1 = n`] THEN
  STRIP_TAC THEN 
  FIRST_ASSUM (MP_TAC o MATCH_MP (ARITH_RULE ` (a + b= &1) ==> (&1 - a = b)`)) THEN REWRITE_TAC[ETA_AX] THEN
  MESON_TAC[vsum]);;

let aff_imp_affcomb = prove
( `!(S:real^N->bool). affine S ==> affine_comb S`,
GEN_TAC THEN REWRITE_TAC[affine;affine_comb] THEN 
DISCH_THEN (LABEL_TAC "1") THEN INDUCT_TAC THENL
[ SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `~(1=0) /\ ~ ( &1 = &0)`]; ALL_TAC ] THEN
REPEAT GEN_TAC THEN REWRITE_TAC[ADD1] THEN ASM_CASES_TAC `( n = 0)` THENL
[ ASM_SIMP_TAC[ARITH_RULE `0+1=1`] THEN REWRITE_TAC[SUM_SING_NUMSEG;NUMSEG_SING;VSUM_SING] THEN
STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LID] THEN FIRST_ASSUM (MATCH_MP_TAC o SPEC `1`) THEN
REWRITE_TAC[IN_SING; GSYM IN]; ALL_TAC ] THEN 
DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "3") (LABEL_TAC "4")) THEN
UNDISCH_TAC (`sum (1..n + 1) (\i. t i) = &1`) THEN UNDISCH_TAC (`~(n=0)`)  THEN
REWRITE_TAC[IMP_IMP] THEN DISCH_THEN (LABEL_TAC "5") THEN
FIRST_ASSUM(MP_TAC o (MATCH_MP comb_trans)) THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
ABBREV_TAC `(f:num->real^N) (i:num) = (&n * (t:num->real) i) % (v:num->real^N) i + (&1 - &n * t i) % v (n + 1)` THEN
FIRST_X_ASSUM ((LABEL_TAC "6") o GSYM) THEN
ABBREV_TAC `(ts:num->real) (i:num) = &1 / &n` THEN
FIRST_X_ASSUM ((LABEL_TAC "7") o GSYM) THEN
FIRST_ASSUM(MATCH_MP_TAC o (SPECL [`(ts:num->real)`;`(f:num->real^N)`])) THEN CONJ_TAC THENL
[ ASM_REWRITE_TAC[SUM_CONST_NUMSEG; ARITH_RULE ` (n+1) - 1 = n`] THEN 
USE_THEN "5" (MP_TAC o (MATCH_MP (TAUT ` A/\B ==> A`))) THEN 
MESON_TAC[REAL_OF_NUM_NOT_EQ;REAL_DIV_LMUL]; GEN_TAC ] THEN ASM_REWRITE_TAC[] THEN
DISCH_THEN (LABEL_TAC "8") THEN 
USE_THEN "1" (MATCH_MP_TAC o (SPECL [`(v:num->real^N) (i:num)`;`(v:num->real^N) ((n:num) +1)`;`(&n * t i):real`])) THEN
CONJ_TAC THENL
[ USE_THEN "4" (MATCH_MP_TAC o (SPEC `i:num`)) THEN UNDISCH_TAC (`(1..n) i`) THEN
  REWRITE_TAC[numseg;IN_ELIM_THM] THEN ARITH_TAC;
  USE_THEN "4" (MATCH_MP_TAC o (SPEC `(n+1):num`)) THEN UNDISCH_TAC (`(1..n) i`) THEN
  REWRITE_TAC[numseg;IN_ELIM_THM] THEN ARITH_TAC]);;

(* The equality between two ways of defining, aff & aff_comb         *)
(* ------------------------------------------------------------------*)

let affine_affcomb = prove
( ` !(S:real^N->bool). affine(aff_comb S)`,
REWRITE_TAC[affine;aff_comb] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `(n:num) + (n':num)` THEN
ABBREV_TAC `(ts:num->real) (i:num) = (if ((1..n) i) then ((t:real)*((t':num->real) i)) else (&1 - t)*((t'':num->real)(i - n)) )` THEN
FIRST_X_ASSUM(LABEL_TAC "ts" o GSYM) THEN
EXISTS_TAC `ts : num->real` THEN
ABBREV_TAC `(vs:num->real^N) (i:num) = (if ((1..n) i) then (v':num->real^N) i else (v'':num->real^N) (i - n) )` THEN
FIRST_X_ASSUM(LABEL_TAC "vs" o GSYM) THEN
EXISTS_TAC `vs:num->real^N` THEN REPEAT CONJ_TAC THENL
[ASM_REWRITE_TAC[GSYM (MATCH_MP SUM_COMBINE_R (ARITH_RULE `1 <= n+1 /\ n <= n+n'`))] THEN
 REWRITE_TAC[MATCH_MP SUM_CASES (SPEC_ALL FINITE_NUMSEG);IN;numseg;IN_ELIM_THM] THEN
SIMP_TAC[ARITH_RULE `((1 <= i /\ i <= n) /\ ~(1 <= i /\ i <= n))= F`] THEN
SIMP_TAC[ARITH_RULE `((n + 1 <= i /\ i <= n + n')/\1 <= i /\ i <= n)= F`] THEN
SIMP_TAC[ARITH_RULE `((n + 1 <= i /\ i <= n + n') /\ ~(1 <= i /\ i <= n))= (1 + n <= i /\ i <= n' + n)`] THEN
REWRITE_TAC[EMPTY_GSPEC;SUM_CLAUSES;REAL_ADD_LID;REAL_ADD_RID;REAL_ADD_AC] THEN
REWRITE_TAC[SUM_LMUL;SUM_OFFSET;GSYM numseg] THEN
UNDISCH_TAC `sum (1..n) (\i. t' i) = &1` THEN REWRITE_TAC[ETA_AX] THEN DISCH_TAC THEN
ASM_REWRITE_TAC[ARITH_RULE `!(i:num). (i+n)-n=i`;REAL_MUL_RID] THEN ARITH_TAC;
ASM_REWRITE_TAC[VMUL_CASES] THEN REWRITE_TAC [MATCH_MP VSUM_CASES (SPECL [`1`;`n+n':num`] FINITE_NUMSEG)] THEN
REWRITE_TAC [IN;IN_ELIM_THM;numseg] THEN 
REWRITE_TAC [ARITH_RULE `((1 <= i /\ i <= n + n') /\ 1 <= i /\ i <= n) = (1 <= i /\ i <= n)`] THEN
REWRITE_TAC [ARITH_RULE `((1 <= i /\ i <= n + n') /\ ~(1 <= i /\ i <= n)) = (1+n <= i /\ i <= n' + n)`] THEN
REWRITE_TAC[GSYM VECTOR_MUL_ASSOC;GSYM numseg;VSUM_LMUL;VSUM_OFFSET;ARITH_RULE `!(i:num).(i+n)-n = i`]; ALL_TAC] THEN
GEN_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THENL
[ UNDISCH_TAC `(1..n) i` ;UNDISCH_TAC `~(1..n) i`] THEN REWRITE_TAC[IMP_IMP;IN;IN_ELIM_THM;numseg] THENL
[REWRITE_TAC[ARITH_RULE `((1 <= i /\ i <= n) /\ 1 <= i /\ i <= n + n')=(1 <= i /\ i <= n)`];
 REWRITE_TAC[ARITH_RULE `(~(1 <= i /\ i <= n) /\ 1 <= i /\ i <= n + n')=(1 <= (i - n) /\ (i-n) <= n')`]] THEN 
DISCH_TAC THENL
[FIRST_ASSUM(MATCH_MP_TAC o (SPEC `i:num`));FIRST_ASSUM(MATCH_MP_TAC o (SPEC `(i-n):num`))] THEN
ASM_REWRITE_TAC[numseg;IN;IN_ELIM_THM]);;

let aff_eq_affcomb = prove
( `!(S:real^N->bool). aff S = aff_comb S`,
GEN_TAC THEN MATCH_MP_TAC  SUBSET_ANTISYM THEN CONJ_TAC THENL
[ REWRITE_TAC[aff] THEN MATCH_MP_TAC(hull_SUBSET) THEN MESON_TAC[SUBSET_affcomb;affine_affcomb];
  REWRITE_TAC[SUBSET;IN;aff_comb] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC ( MATCH_MP aff_imp_affcomb (SPEC `S:real^N->bool` affine_aff)) THEN 
  ASM_REWRITE_TAC[affine_comb] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o (SPECL [`n:num`;`t:num->real`;`v:num->real^N`])) THEN
  ASM_REWRITE_TAC[] THEN GEN_TAC THEN FIRST_X_ASSUM (MP_TAC o (SPEC `i:num`)) THEN
  MATCH_MP_TAC(TAUT `(B==>C) ==> ((A==>B)==> A ==> C)`) THEN
  MP_TAC (SPEC `S:real^N->bool` SUBSET_aff) THEN MESON_TAC [SUBSET;IN]]);;

let aff_2 = prove (` ! (a:real^N) (b:real^N). aff {a,b} = {u| ?(t:real). u = t % a + (&1 - t) % b}`,
REPEAT GEN_TAC THEN (ABBREV_TAC `(M:real^N ->bool) = {u| ?(t:real). u = t % a + (&1 - t) % b}`) THEN 
FIRST_X_ASSUM(LABEL_TAC "M" o GSYM) THEN
MATCH_MP_TAC(SUBSET_ANTISYM) THEN CONJ_TAC THENL
[ REWRITE_TAC[aff] THEN MATCH_MP_TAC(hull_SUBSET) THEN CONJ_TAC THENL
  [ ASM_REWRITE_TAC[SET_RULE ` {a,b} SUBSET M <=> (a IN M /\ b IN M)`;IN_ELIM_THM;IN] THEN
    CONJ_TAC  THENL [EXISTS_TAC `&1`; EXISTS_TAC `&0`] THEN VECTOR_ARITH_TAC;
    ASM_REWRITE_TAC[affine;IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC ` t * t' + (&1- t) * t''` THEN 
    REWRITE_TAC[ARITH_RULE ` &1 - (t * t' + (&1 - t) * t'') = t * (&1 - t') + (&1 - t) * (&1 - t'')`] THEN
    VECTOR_ARITH_TAC
  ] ;
  ASM_REWRITE_TAC[SUBSET;IN_ELIM_THM;IN;aff_eq_affcomb;aff_comb] THEN GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `(ts: num ->real) i = ( if ( i = 1) then t else ( &1 - t))` THEN
  FIRST_X_ASSUM(LABEL_TAC "ts" o GSYM) THEN 
  ABBREV_TAC `(vs: num ->real^N) i = ( if ( i = 1) then a else b)` THEN
  FIRST_X_ASSUM(LABEL_TAC "vs" o GSYM) THEN 
  EXISTS_TAC `2` THEN EXISTS_TAC `(ts:num->real)` THEN EXISTS_TAC ` (vs:num->real^N) ` THEN
  ASM_REWRITE_TAC[SUM_2;VSUM_2;ARITH_RULE `~(2=1) /\ (t + &1 - t = &1)`] THEN
  GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN ONCE_REWRITE_TAC[GSYM IN] THEN SET_TAC[]
]);;


(* convex, added by thales *)

let conv0pt = prove(`conv {} = {}:real^A->bool`,
   REWRITE_TAC[conv;sgn_ge;affsign;UNION_EMPTY;FUN_EQ_THM;elimin NOT_IN_EMPTY;lin_combo;SUM_CLAUSES]
   THEN REAL_ARITH_TAC);;
		    
let conv1pt = prove(`!u. conv {u:real^A} = {u}`,
  REWRITE_TAC[conv;sgn_ge;affsign;FUN_EQ_THM;UNION_EMPTY;lin_combo;SUM_SING;VSUM_SING;elimin IN_SING] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC[TAUT `(p <=> q) = ((p ==> q) /\ (q ==> p))`] THEN
  REPEAT STRIP_TAC THENL
  [ASM_MESON_TAC[VECTOR_MUL_LID];
  ASM_REWRITE_TAC[]] THEN
  EXISTS_TAC `\ (v:real^A). &1` THEN
  MESON_TAC[VECTOR_MUL_LID;REAL_ARITH `&0 <= &1`]
		   );;



(*


let conv_insert = prove(`!S (v:real^3).
     FINITE S ==> 
     (conv (v INSERT S) = {x | ?s t. (conv S s) /\ &0 <= t /\ t <= &1 /\ (x = t % s + (&1-t) % v)})`,
   REWRITE_TAC[conv;affsign;sgn_ge;FUN_EQ_THM;lin_combo;UNION_EMPTY];
   SIMP_TAC[FINITE_INSERT;FINITE_RULES;VSUM_CLAUSES;SUM_CLAUSES];
   REPEAT STRIP_TAC;
   ASM_REWRITE_TAC[elimin IN_INSERT;IN_ELIM_THM];
   REWRITE_TAC[TAUT `(p <=> q) = ((p ==> q) /\ (q ==> p))`] ;
   (*  *)
   DISJ_CASES_TAC (TAUT `(v IN S) \/ ~((v:real^3) IN S)`);;
   
   REPEAT STRIP_TAC;
   EXISTS_TAC `x:real^3`;
   EXISTS_TAC `&1`;
   ASM_REWRITE_TAC[REAL_ARITH `&0 <= (&1) /\ (&1 <= (&1)) /\ (&1 - &1 = &0)`;VECTOR_MUL_LID;VECTOR_MUL_LZERO;VECTOR_ADD_RID;];
   ASM_MESON_TAC[];
   (* 2 *)
   ABBREV_TAC `g = \w. (if (w=v:real^3) then (t* f v + (&1 - t)) else t * f w)`;
   EXISTS_TAC `g:real^3->real`;
   CONJ_TAC;
   EXPAND_TAC "g";
   ASM_REWRITE_TAC[];
   UNDISCH_TAC `FINITE (S:real^3->bool)`;
   (* to here *)
   


*)
   

