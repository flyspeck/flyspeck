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

(*Prove the most basic theorem of multiplying both sides with the same non-zero integer (homogeneity)*)
let homogeneity_thm = prove();;

let MAP_LENGTH_PRESERVING = prove(`!cs. LENGTH (MAP (f:A->B) (cs:A list)) = LENGTH cs`,
 LIST_INDUCT_TAC THENL
 [ REWRITE_TAC[MAP; LENGTH];
   REWRITE_TAC[LENGTH] THEN
   REWRITE_TAC[MAP;LENGTH] THEN
   UNDISCH_TAC `LENGTH (MAP (f:A->B) (t:A list)) = LENGTH t` THEN
   REWRITE_TAC[prove(`a = b ==> SUC a = SUC b`, MESON_TAC[])]
 ] );;
 
let LIST_LENGTH_ZERO = prove(`!(cs:A list). LENGTH cs = 0 <=> cs = []`,
REPEAT GEN_TAC THEN	EQ_TAC THENL
[
	SPEC_TAC (`cs:A list` , `cs:A list`) THEN LIST_INDUCT_TAC THENL
	[
		REWRITE_TAC[LENGTH];
		REWRITE_TAC[LENGTH] THEN REWRITE_TAC[prove(`( SUC a = 0 ) <=> F`, ARITH_TAC)]
	];
	DISCH_TAC THEN (ASM_REWRITE_TAC[]) THEN REWRITE_TAC[LENGTH]
]
);;

g `( ~(a = &0) ) ==> !xs cs.( is_solution xs (cs,b) <=> is_solution xs ( MAP (\c. a*c) cs, a*b ) )`;;
e  DISCH_TAC;;
e (LIST_INDUCT_TAC);;
	e (REWRITE_TAC[is_solution]);;
	e (REWRITE_TAC[MAP_LENGTH_PRESERVING]);;
	e (REWRITE_TAC[prove(` ( (A /\ B) <=> (A /\ C) ) <=> ( A ==> ( B <=> C ) )`, MESON_TAC[])]);;
	e (REWRITE_TAC[prove(`LENGTH [] = 0`, REWRITE_TAC [LENGTH])]);;
	e (GEN_TAC);;
	e (REWRITE_TAC[prove(`0=a <=> a=0`, ARITH_TAC)]);;
	e (REWRITE_TAC[LIST_LENGTH_ZERO]);;
	e (DISCH_TAC);;
	e (ASM_REWRITE_TAC[]);;
	e (REWRITE_TAC[ITLIST2]);;
	e (REWRITE_TAC[MAP]);;
	e (UNDISCH_TAC `~ (a = &0)`);;
	e (REWRITE_TAC[ITLIST2]);;
	e (MESON_TAC[REAL_FIELD `~(a = &0) ==> (&0 = b <=> &0 = a * b)`]);;
	
	e (REWRITE_TAC[is_solution]);;
	e (REWRITE_TAC[MAP_LENGTH_PRESERVING]);;
	e (REWRITE_TAC[prove(` ( (A /\ B) <=> (A /\ C) ) <=> ( A ==> ( B <=> C ) )`, MESON_TAC[])]);;
	e (REWRITE_TAC[LENGTH]);;
	e (LIST_INDUCT_TAC);;
		e (REWRITE_TAC[prove(`LENGTH [] = 0`, REWRITE_TAC [LENGTH])]);;
		e (REWRITE_TAC[prove(`( SUC a = 0) <=> F`, ARITH_TAC)]);;
		
		e (REWRITE_TAC[LENGTH]);;
		e (REWRITE_TAC[prove(`SUC a = SUC b <=> a = b`, ARITH_TAC)]);;
		e (REWRITE_TAC[ITLIST2]);;
		e (REWRITE_TAC[MAP]);;
		e (REWRITE_TAC[ITLIST2]);;
		e (REWRITE_TAC[MAP]);;
		e (REWRITE_TAC[ITLIST2]);;

g `!t t'.(LENGTH t = LENGTH t') ==> ITLIST2 (\c x s. c * x + s) (MAP (\c. a * c) t') t (&0) = a * ITLIST2 (\c x s. c * x + s) t' t (&0)`;;
e LIST_INDUCT_TAC;;
	e (REWRITE_TAC[prove(`LENGTH [] = 0`, REWRITE_TAC [LENGTH])]);;
	e (REWRITE_TAC[prove(`0=a <=> a=0`, ARITH_TAC)]);;
	e (REWRITE_TAC[LIST_LENGTH_ZERO]);;
	e (GEN_TAC);;
	e (DISCH_TAC);;
	e (ASM_REWRITE_TAC[]);;
	e (REWRITE_TAC[MAP]);;
	e (REWRITE_TAC[ITLIST2]);;
	e (MESON_TAC[REAL_FIELD `&0 = a * &0`]);;
	
	e (REWRITE_TAC[LENGTH]);;
	e LIST_INDUCT_TAC;;
		e (REWRITE_TAC[LENGTH]);;
		e (MESON_TAC[NOT_SUC]);;
		
		e (REWRITE_TAC[LENGTH]);;
		e (REWRITE_TAC[SUC_INJ]);;
		e (REWRITE_TAC[MAP; ITLIST2]);;
		e (REWRITE_TAC[prove(`a * (h' * h + ITLIST2 (\c x s. c * x + s) t' t (&0)) = a * h' * h + a * ITLIST2 (\c x s. c * x + s) t' t (&0)`, ARITH_TAC)]);;
		e (REWRITE_TAC[prove(`(a * h') * h + ITLIST2 (\c x s. c * x + s) (MAP (\c. a * c) t') t (&0) = a * h' * h + ITLIST2 (\c x s. c * x + s) (MAP (\c. a * c) t') t (&0)`, ARITH_TAC)]);;
		
		prove(` ( a * h' * h + ITLIST2 (\c x s. c * x + s) (MAP (\c. a * c) t') t (&0) = a * h' * h + a * ITLIST2 (\c x s. c * x + s) t' t (&0) ) <=> 
		( ITLIST2 (\c x s. c * x + s) (MAP (\c. a * c) t') t (&0) = ITLIST2 (\c x s. c * x + s) t' t (&0) )`, ARITH_TAC);;
		
		e DISCH_TAC;;
		e (REWRITE_TAC[prove(`a * h' * h + xx = a * h' * h + a * yy <=> xx = a * yy`, ARITH_TAC)]);;
		e (ASM_REWRITE_TAC[]);;
		
		
		
		
		
		
		
		
		
		