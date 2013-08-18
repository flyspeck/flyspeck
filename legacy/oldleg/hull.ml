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


(* VSUM_2 -> hull_error.ml *)

let REAL_OF_NUM_NOT_EQ = prove
   ( `!n m. ~(m = n) <=> ~(&m = &n)`, MESON_TAC[REAL_OF_NUM_EQ]);;

let VMUL_CASES = prove
  (`!(P:A->bool) (t:A->real) (t':A->real) (v:A->real^N) (v':A->real^N). (if P i then t i else t' i) % (if P i then v i else v' i) = (if P i then ( t i % v i) else (t' i % v' i))`,
  REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[]);;

(* Relation between affine and affine_comb                         *)
(* --------------------------------------------------------------- *)

(* affcomb_imp_aff -> hull_error.ml *)


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



(* aff_imp_affcomb -> hull_error.ml *)


(* The equality between two ways of defining, aff & aff_comb         *)
(* ------------------------------------------------------------------*)

(* affine_affcomb -> hull_error.ml *)

(* aff_eq_affcomb  -> hull_error.ml *)

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

