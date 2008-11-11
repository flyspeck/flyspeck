(* The first change for toplevel.ml *)
needs "Multivariate/vectors.ml";;

prioritize_real();;

(* B( x, r) *)
let open_ball = new_definition `open_ball (x:real^3) (r:real)= { y | norm(y-x)< r }`;;  

(* Packing Lambda *)
(* packing already defined in definitione_kepler.ml 
let packing = new_definition `packing (Lambda:real^3 -> bool) = (!x y. ( x IN Lambda) /\ ( y IN Lambda) /\ ~(x = y) ==> norm(x - y) >= &2 )`;;
*)

(* B( x , r , Lambda) *) 
let ball3_lambda = new_definition ` ball3_lambda (x:real^3) (r:real) (Lambda:real^3 -> bool) = ((open_ball x r ) INTER ( UNIONS ( IMAGE (\v. open_ball v (&1)
) Lambda ) ))`;;
(* Delta ( Lambda x r) This definition is not good because I don't know where to load the definition of Vol 3 *)
(*
let delta_finite = new_definition `delta_finite (x:real^3) (r:real) (Lambda:real^3 -> bool) = (( vol 3 ( ball3_lambda x r Lambda) ) / ( vol 3 (open_ball x r )))`;;
*)
(* Lambda x r *)
let truncated_packing = new_definition ` truncated_packing x r Lambda = Lambda INTER (ball3_lambda x r Lambda) `;;


(* Beginning of Proving Lemma 7.1 (lemmaseo)  that needs Examples/floor.ml; FLOOR_EQ , VECTOR_SUB_COMPONENT_3 theorem and lemmaseoo proved in following *)
(*
 g ` packing Lambda ==> FINITE (truncated_packing x r Lambda )`;;
*)
needs "Examples/floor.ml";;

let FLOOR_EQ = prove
  (`!(x:real) y. floor x = floor y ==> abs(x - y) < &1`,
   REPEAT GEN_TAC THEN STRIP_TAC THEN SIMP_TAC[ GSYM REAL_BOUNDS_LT]
  THEN MP_TAC(SPEC `x:real` FLOOR_FRAC) THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC)
  THEN MP_TAC(SPEC `y:real` FLOOR_FRAC) THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC)
  THEN FIRST_X_ASSUM(SUBST1_TAC) THEN REWRITE_TAC[REAL_ARITH `(floor y + frac x) - (floor y + frac y) = frac x - frac y`]
  THEN UNDISCH_TAC `&0 <= frac x` THEN UNDISCH_TAC `&0 <= frac y` THEN UNDISCH_TAC `frac x < &1` THEN UNDISCH_TAC `frac y < &1`
  THEN REAL_ARITH_TAC );;

let VECTOR_SUB_COMPONENT_3 = prove 
  (`!(x:real^3) (y:real^3). x$1 - y$1 = (x - y)$1 /\ x$2 - y$2 = (x - y)$2 /\ x$3 - y$3 = (x - y)$3`,
  REPEAT GEN_TAC THEN MP_TAC (ISPECL [`x:real^3`; `y:real^3`; `1`] VECTOR_SUB_COMPONENT) THEN
  MP_TAC (ISPECL [`x:real^3`; `y:real^3`; `2`] VECTOR_SUB_COMPONENT) THEN
  MP_TAC (ISPECL [`x:real^3`; `y:real^3`; `3`] VECTOR_SUB_COMPONENT) THEN REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC);;
let lemmaseoo = prove
  (`!(p:real^3) x y. (!(v:real^3). f v = ( floor (&2 * (v$1 - p$1)),floor (&2 * (v$2 - p$2)),floor (&2 * (v$3 - p$3)))) /\ norm (x - y) >= &2 ==> ~(f x = f y) `,
    REPEAT GEN_TAC THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[PAIR_EQ] THEN REPEAT STRIP_TAC
  THEN REPEAT (FIRST_X_ASSUM(MP_TAC o (MATCH_MP FLOOR_EQ)))
  THEN REWRITE_TAC[REAL_ARITH `(abs (&2 * (x$1 - p$1) - &2 * (y$1 - p$1)) < &1) <=> abs(x$1 - y$1) < &1/ &2` ]
  THEN REWRITE_TAC[REAL_ARITH `(abs (&2 * (x$2 - p$2) - &2 * (y$2 - p$2)) < &1) <=> abs(x$2 - y$2) < &1/ &2` ]
  THEN REWRITE_TAC[REAL_ARITH `(abs (&2 * (x$3 - p$3) - &2 * (y$3 - p$3)) < &1) <=> abs(x$3 - y$3) < &1/ &2` ]
  THEN REWRITE_TAC[VECTOR_SUB_COMPONENT_3] THEN REPEAT STRIP_TAC THEN MP_TAC (ISPEC `x:real^3 - y` NORM_LE_L1)
  THEN REWRITE_TAC[SUM_3;DIMINDEX_3]
  THEN UNDISCH_TAC`norm (x:real^3 - y) >= &2`
  THEN UNDISCH_TAC`abs ((x:real^3 - y)$1) < &1 / &2`
  THEN UNDISCH_TAC`abs ((x:real^3 - y)$2) < &1 / &2`
  THEN UNDISCH_TAC`abs ((x:real^3 - y)$3) < &1 / &2`
  THEN REAL_ARITH_TAC );;
(* Lemmaseotw
  g ` !p. (!v. f v = (floor(&2 * ( v$1 - p$1)), floor(&2 * (v$2 - p$2)), floor(&2 * (v$3 - p$3)))) /\ packing Lambda 
  ==> INJ f Lambda (int^3) `;;
*)
