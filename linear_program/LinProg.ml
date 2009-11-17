(*Define the notion of solution*)
let is_solution = define `is_solution xs (cs,b) <=>
         LENGTH xs = LENGTH cs /\
         ITLIST2 (\c x s. c * x + s) cs xs (&0) = b`;;

g `~ (is_solution [ #3 ] ( [ #2 ], #5 ))`;;
e (REWRITE_TAC [is_solution]);;
e (DISJ_TAC);;
e (REWRITE_TAC [prove(`~(A /\ B) <=> (~A) \/ (~B)`, MESON_TAC[])]);;
e (DISJ2_TAC);;
e (REWRITE_TAC[ITLIST2]);;
e (ARITH_TAC);;

(*Prove the most basic theorem of multiplying both sides with the same non-zero integer*)
let multiply_both_sides_thm = prove();;

g ` ( ~(a = &0) ) ==> ( is_solution xs (cs,b) <=> is_solution xs ( MAP (\c. a*c) cs, a*b ) )`;;
e (REWRITE_TAC[is_solution; ITLIST2; MAP]);;
e (DISCH_TAC);;

g `LENGTH (MAP (f:A->B) (cs:A list)) = LENGTH cs`;;
g `(cs:A list) = [] \/ (cs = CONS h t)`;;
