(*Define the notion of solution*)
let is_solution = define `is_solution xs (cs,b) <=>
         LENGTH xs = LENGTH cs /\
         ITLIST2 (\c x s. c * x + s) cs xs (&0) = b`;;

(*Example*)
(*g `~ (is_solution [ #3 ] ( [ #2 ], #5 ))`;;
e (REWRITE_TAC [is_solution]);;
e (DISJ_TAC);;
e (REWRITE_TAC [prove(`~(A /\ B) <=> (~A) \/ (~B)`, MESON_TAC[])]);;
e (DISJ2_TAC);;
e (REWRITE_TAC[ITLIST2]);;
e (ARITH_TAC);;
*)

(*Useful tactic supporting double list induction- written by John Harrison*)
let LIST2_INDUCT_TAC =
  let list2_INDUCT = prove
   (`!P:(A)list->(B)list->bool.
         P [] [] /\
         (!h1 t1 h2 t2. P t1 t2 ==> P (CONS h1 t1) (CONS h2 t2))
         ==> !l1 l2. LENGTH l1 = LENGTH l2 ==> P l1 l2`,
     GEN_TAC THEN STRIP_TAC THEN
     LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
     ASM_SIMP_TAC[LENGTH; NOT_SUC; SUC_INJ]) in
  MATCH_MP_TAC list2_INDUCT THEN
  CONJ_TAC THENL [ALL_TAC; REPLICATE_TAC 4 GEN_TAC THEN DISCH_TAC];;

(*Prove the most basic theorem of multiplying both sides with the same non-zero integer (homogeneity)*)
let homogeneity_thm = prove();;

g `( ~(a = &0) ) ==> !xs cs.( is_solution xs (cs,b) <=> is_solution xs ( MAP (\c. a*c) cs, a*b ) )`;;
e DISCH_TAC;;
e (REWRITE_TAC[is_solution; LENGTH_MAP]);;
e (REWRITE_TAC[TAUT` (a/\b<=>a/\c) = (a ==> (b<=>c))`]);;

e LIST2_INDUCT_TAC;;
	e (REWRITE_TAC[MAP; ITLIST2]);;
	e (UNDISCH_TAC `~(a = &0)`);;
	e (REWRITE_TAC[REAL_FIELD `~(a = &0) ==> (&0 = b <=> &0 = a * b)`]);;
	
	e (REWRITE_TAC[MAP; ITLIST2]);;
	e (REWRITE_TAC[ARITH_RULE `(a:real)+b=c <=> b=c-a`]);;
	e (REWRITE_TAC[ARITH_RULE `((a:real)* b) * c = a * (b * c)`]);;
	e (REWRITE_TAC[ARITH_RULE `(a:real) * b - a * c = a * (b - c)`]);;
	e (ONCE_ASM_REWRITE_TAC[]);;

let mylemm = prove(`!t t'.(LENGTH t = LENGTH t') ==> ITLIST2 (\c x s. c * x + s) (MAP (\c. a * c) t') t (&0) = a * ITLIST2 (\c x s. c * x + s) t' t (&0)`,
(*SPEC_TAC (`t':real list`, `t':real list`) THEN
SPEC_TAC (`t:real list`, `t: real list`) THEN*)
LIST2_INDUCT_TAC THEN
REWRITE_TAC[MAP; ITLIST2] THENL [
	ARITH_TAC;

	REWRITE_TAC[ARITH_RULE`((a:real) * b) * c = a * (b * c)`] THEN
	ASM_REWRITE_TAC[] THEN
	REWRITE_TAC[ARITH_RULE`(a:real) * b + a * c = a * (b + c)`] ]);;

