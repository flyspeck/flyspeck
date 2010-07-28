(*Define the notion of solution*)
let is_solution = define `is_solution xs (cs,b) <=>
         LENGTH xs = LENGTH cs /\
         ITLIST2 (\c x s. c * x + s) cs xs (&0) = b`;;

(*Useful tactic supporting double list induction -- written by John Harrison*)
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
let homogeneity_thm = prove(`!a b xs cs. ( ~(a = &0) ) ==> ( is_solution xs (cs,b) <=> is_solution xs ( MAP (\c. a*c) cs, a*b ) )`,
REPEAT GEN_TAC THEN
REWRITE_TAC[is_solution; LENGTH_MAP] THEN
REWRITE_TAC[TAUT` (a/\b<=>a/\c) = (a ==> (b<=>c))`] THEN
REPEAT DISCH_TAC THEN
UNDISCH_TAC `~(a = &0)` THEN
SPEC_TAC (`b:real`, `b:real`) THEN
SPEC_TAC (`a:real`, `a:real`) THEN
UNDISCH_TAC `LENGTH (xs:real list) = LENGTH (cs:real list)` THEN
SPEC_TAC (`cs: real list`,`cs: real list`) THEN
SPEC_TAC (`xs: real list`,`xs: real list`) THEN
LIST2_INDUCT_TAC THENL [
	REPEAT GEN_TAC THEN
	REWRITE_TAC[MAP; ITLIST2] THEN
	REWRITE_TAC[REAL_FIELD `~(a = &0) ==> (&0 = b <=> &0 = a * b)`];
	
	REWRITE_TAC[MAP; ITLIST2] THEN
	REWRITE_TAC[ARITH_RULE `(a:real)+b=c <=> b=c-a`] THEN
	REWRITE_TAC[ARITH_RULE `((a:real)* b) * c = a * (b * c)`] THEN
	REWRITE_TAC[ARITH_RULE `(a:real) * b - a * c = a * (b - c)`] THEN
	ASM_SIMP_TAC[]
] );;

