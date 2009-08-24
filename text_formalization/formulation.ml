 (* Nguyen Tat Thang *)

needs "volume.ml";;
(* The finiteness section in chapter Volume *)


let packing = new_definition `packing (S:real^3 -> bool) = (!u v. S u /\ S v /\ ~(u = v) ==> (&2 <= dist( u, v)))`;;

let map3=new_definition `(map3:real^3 -> real^3 ->real^3) x p = lambda i. floor(&2* (x$i - p$i))`;;

let bound_square=prove( `!(a:real)(b:real)(c:real). (a<=b /\ b<=c) ==> b pow 2 <= max ( a pow 2) (c pow 2)`,
REPEAT STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH `&0<= b \/ b< &0`)
THENL [MP_TAC(MESON[REAL_POW_LE2] `&0<= b /\ b<= c ==> b pow 2 <= c pow 2`) THEN ASM_SIMP_TAC[REAL_LE_MAX];MP_TAC(REAL_ARITH `b< &0 /\a<= b ==> &0<= -- b /\ --b<= --a`)] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC(MESON[REAL_POW_LE2] `&0<= -- b /\ --b<= --a ==> --b pow 2 <= --a pow 2`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[REAL_LE_MAX;REAL_ARITH `--(x:real) pow 2= x pow 2`]);;


let cauchy_ineq=prove( `!(a:real)(b:real). (a+b) pow 2<= &2* (a pow 2+ b pow 2)`,REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[REAL_ARITH `(x:real) <= y <=> &0<= y - x`] THEN REWRITE_TAC[REAL_FIELD `&2 * (a pow 2 + b pow 2) - (a + b) pow 2 = (a- b) pow 2`]
			 THEN REWRITE_TAC[REAL_FIELD `(a- b) pow 2 = (a-b) * (a-b)`;REAL_LE_SQUARE]);;

let bdt_emveque=prove(`!(r:real). &0 <= &8* (r pow 2) + &6`,GEN_TAC 
THEN MP_TAC(MESON[REAL_LE_SQUARE; REAL_FIELD `r pow 2= r * r`] `&0<= r pow 2`) THEN 
DISCH_TAC THEN MP_TAC(MESON[REAL_LE_MUL;REAL_ARITH `&0<= &8`] `&0<= r pow 2 ==> &0<= &8* (r pow 2)`)
THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;


let norm_abs= MESON[NORM_POS_LE;REAL_ARITH `&0<= a ==> abs a= a`] `!(x:real^3 ). norm x= abs (norm x)`;;

let bp_bdt=prove( `!(a:real)(b:real). (&0<= a /\ &0<= b) ==> (a< b <=> a pow 2 < b pow 2)`,REPEAT GEN_TAC 
THEN REWRITE_TAC[GSYM REAL_ABS_REFL] THEN ONCE_REWRITE_TAC[MESON[] `x:real = y<=> y=x`] THEN STRIP_TAC 
THEN ASM_MESON_TAC[REAL_LT_SQUARE_ABS]);;

let bdt_emnguchua=prove( `!(k:real). floor (&2* k)* floor( &2*k)<= &2*( &4* (k pow 2) + &1)`,
 GEN_TAC  THEN MP_TAC(SPEC ` &2*k:real` FLOOR) THEN REWRITE_TAC[REAL_ARITH `a:real < b+ &1 <=> a- &1 < b`]
   THEN STRIP_TAC THEN MP_TAC(SPECL [`&2 * k - &1:real`;`floor (&2 * k):real`;`&2 * k` ] bound_square)
   THEN ASM_SIMP_TAC[REAL_ARITH `a:real < b ==> a<= b`] 
   THEN DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `floor (&2 * k) pow 2 <= max ((&2 * k - &1) pow 2) ((&2 * k) pow 2) /\ max ((&2 * k - &1) pow 2) ((&2 * k) pow 2) <= &2 * (&4 * k pow 2 + &1) ==> floor (&2 * k) * floor (&2 * k) <= &2 * (&4 * k pow 2 + &1)`)
   THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[REAL_MAX_LE] THEN SIMP_TAC[cauchy_ineq;REAL_FIELD `&2 * k - &1= (&2 * k) + ( -- &1)`;REAL_FIELD `(&2 * k) pow 2 = &4 * (k pow 2 )`; REAL_ARITH `( -- &1) pow 2 = &1`] THEN SIMP_TAC[cauchy_ineq;REAL_FIELD `&4 * (k pow 2 )= (&2 * k) pow 2`;
 REAL_ARITH ` &1= ( -- &1) pow 2`] 
THEN ONCE_REWRITE_TAC[REAL_ARITH `&2 * ((&2 * k) pow 2 + &1)= &2 * ((&2 * k) pow 2 +  ( -- &1) pow 2)`]
   THEN REWRITE_TAC[cauchy_ineq] THEN REWRITE_TAC[REAL_FIELD `(&2 * k) pow 2 <= &2 * ((&2 * k) pow 2 + -- &1 pow 2) <=> &4* (k pow 2)<= &8* (k pow 2) + &2`]
   THEN ONCE_REWRITE_TAC[REAL_ARITH `a<=b <=> &0<= b-a `;REAL_FIELD `&8 * k pow 2 + &2- &4 * k pow 2= &4 * k pow 2 + &2`]
     THEN ONCE_REWRITE_TAC[REAL_FIELD `(&8 * k pow 2 + &2) - &4 * k pow 2= &4 * k pow 2 + &2`]
   THEN MP_TAC(MESON[REAL_LE_SQUARE; REAL_FIELD `k pow 2 = k * k`] `&0<= k pow 2`) THEN 
DISCH_TAC THEN MP_TAC(MESON[REAL_LE_MUL;REAL_ARITH `&0<= &4`] `&0<= k pow 2 ==> &0<= &4* (k pow 2)`)
THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;



let map3_define=prove(`!(v:real^3)(p:real^3)(r:real). &0<=r /\ v IN ball(p,r) 
==> map3 p v IN ball(vec 0, sqrt(&8* (r pow 2) + &6))`,REPEAT GEN_TAC THEN REWRITE_TAC[ball;IN_ELIM_THM]
  THEN REWRITE_TAC[dist;VECTOR_ARITH `vec 0 - map3 (p:real^3) v = -- map3 p v`;NORM_NEG]
  THEN MP_TAC (SPEC `(&8* (r pow 2) + &6):real` SQRT_POS_LE)
  THEN SIMP_TAC[bdt_emveque] THEN DISCH_TAC THEN ASSUME_TAC(ISPEC `(p:real^3- v):real^3` NORM_POS_LE) THEN ASSUME_TAC(ISPEC `(map3 (p:real^3) v):real^3` NORM_POS_LE) THEN REWRITE_TAC[MESON[] `a/\b ==> c <=> a==> b==> c`]
  THEN DISCH_TAC THEN ASM_SIMP_TAC[bp_bdt] THEN SIMP_TAC[NORM_POW_2;DOT_3]  THEN REWRITE_TAC[map3]
  THEN SIMP_TAC[LAMBDA_BETA;DIMINDEX_3;ARITH_RULE `1<=1/\1<=3 /\ 1<=2 /\ 2<= 3 /\ 1<= 3 /\ 3<=3`]
  THEN DISCH_TAC THEN MP_TAC(SPEC `((p:real^3)$1 - (v:real^3)$1):real` bdt_emnguchua) THEN MP_TAC(SPEC `((p:real^3)$2 - (v:real^3)$2):real` bdt_emnguchua)
     THEN MP_TAC(SPEC `((p:real^3)$3 - (v:real^3)$3):real` bdt_emnguchua)
  THEN REPEAT DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `q:real <= &2 * (&4 * ((p:real^3)$1 - (v:real^3)$1) pow 2 + &1) + 
 &2 * (&4 * (p$2 - v$2) pow 2 + &1) + &2 * (&4 * (p$3 - v$3) pow 2 + &1) /\  &2 * (&4 * (p$3 - v$3) pow 2 + &1) + 
 &2 * (&4 * (p$2 - v$2) pow 2 + &1) + &2 * (&4 * (p$1 - v$1) pow 2 + &1) <   sqrt (&8 * r pow 2 + &6) pow 2 
==> q<  sqrt (&8 * r pow 2 + &6) pow 2`)
  THEN ASM_SIMP_TAC[REAL_ARITH `floor (&2 * ((p:real^3)$3 - (v:real^3)$3)) * floor (&2 * (p$3 - v$3)):real <=
      &2 * (&4 * (p$3 - v$3) pow 2 + &1) /\ floor (&2 * (p$2 - v$2)) * floor (&2 * (p$2 - v$2)) <=
      &2 * (&4 * (p$2 - v$2) pow 2 + &1) /\ floor (&2 * (p$1 - v$1)) * floor (&2 * (p$1 - v$1)) <=
      &2 * (&4 * (p$1 - v$1) pow 2 + &1) ==> floor (&2 * (p$1 - v$1)) * floor (&2 * (p$1 - v$1)) +
 floor (&2 * (p$2 - v$2)) * floor (&2 * (p$2 - v$2)) +
 floor (&2 * (p$3 - v$3)) * floor (&2 * (p$3 - v$3)) <=
 &2 * (&4 * (p$1 - v$1) pow 2 + &1) +
 &2 * (&4 * (p$2 - v$2) pow 2 + &1) +
 &2 * (&4 * (p$3 - v$3) pow 2 + &1)`]
  THEN REWRITE_TAC[REAL_FIELD `&2 * (&4 * ((p:real^3)$3 - (v:real^3)$3) pow 2 + &1) +
 &2 * (&4 * (p$2 - v$2) pow 2 + &1) +
 &2 * (&4 * (p$1 - v$1) pow 2 + &1)= &8 * ( (p$1 - v$1) pow 2 + (p$2 - v$2) pow 2 + (p$3 - v$3) pow 2) + &6`]
  THEN ASSUME_TAC (SPEC  `r:real` bdt_emveque) THEN ASM_SIMP_TAC[SQRT_POW_2]
  THEN REWRITE_TAC[REAL_ARITH `a + &6 < b+ &6 <=> a< b`] THEN SIMP_TAC[REAL_ARITH `&0< &8`;REAL_LT_LMUL_EQ]
  THEN ASM_REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT;DIMINDEX_3] THEN REWRITE_TAC[REAL_ARITH `a pow 2= a*a`]
  THEN ASM_MESON_TAC[REAL_ARITH `a pow 2= a*a`]);;


let floor_ineq=prove( `!(x:real)(y:real). floor x = floor y ==> abs (x- y)< &1`,REPEAT STRIP_TAC THEN MP_TAC(SPEC `x:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MP_TAC(SPEC `y:real` FLOOR)
			 THEN REPEAT STRIP_TAC THEN MP_TAC (REAL_ARITH `floor y <= x /\ y < floor y + &1 ==> y< x+ &1`)
			 THEN ASM_REWRITE_TAC[] THEN MP_TAC (REAL_ARITH `floor y <= y /\ x < floor y + &1 ==> x< y+ &1`)
			 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;


let bdt_canbatrenbon=prove( `sqrt ( &3/ &4)< &2`,MP_TAC (SPEC `&3 / &4 :real` SQRT_POS_LE) THEN REWRITE_TAC[REAL_ARITH `&0<= &3/ &4`] THEN REWRITE_TAC[REAL_ARITH ` &0<=a:real <=> a = abs a`] THEN MP_TAC(SPEC `&2:real` REAL_ABS_REFL)
			      THEN REWRITE_TAC[REAL_ARITH ` &0 <= &2`] THEN REWRITE_TAC[MESON[] `a:real = b ==> c:real = d ==> c< b <=> a:real = b ==> c:real = d ==> d< a`] THEN REWRITE_TAC[REAL_LT_SQUARE_ABS] THEN SIMP_TAC[REAL_ARITH `&2 pow 2 = &4`;SQRT_POW_2;REAL_ARITH `&0<= &3/ &4`] THEN REAL_ARITH_TAC);;


let inj_map3=prove(`!(p:real^3)(r:real) (S:real^3 -> bool). (&0 <= r) /\ (packing S) ==> INJ (map3 p) (S INTER ball(p,r)) (int_ball (vec 0) (sqrt( &8 * (r pow 2) + &6)))`,REPEAT GEN_TAC THEN REWRITE_TAC[INJ] THEN STRIP_TAC THEN REWRITE_TAC[int_ball;IN_ELIM_THM] THEN REWRITE_TAC[IN_INTER;hinhcau_ball] THEN ASM_SIMP_TAC[map3_define] THEN REWRITE_TAC[IN_ELIM_THM]  THEN REWRITE_TAC[map3] THEN SIMP_TAC[LAMBDA_BETA;DIMINDEX_3;ARITH_RULE `1<=1/\1<=3 /\ 1<=2 /\ 2<= 3 /\ 1<= 3 /\ 3<=3`]
		     THEN REWRITE_TAC[FLOOR;GSYM INTEGER_IS_INT] THEN REWRITE_TAC[CART_EQ]
		     THEN SIMP_TAC[LAMBDA_BETA;DIMINDEX_3] THEN REPEAT GEN_TAC THEN REWRITE_TAC[FORALL_3]
		     THEN REWRITE_TAC[MESON[] `a/\b/\c/\d/\e ==> f <=> a==>b==>c==>d ==>e==>f`]
		     THEN REPLICATE_TAC 5 DISCH_TAC THEN MP_TAC(SPECL [`&2 * ((p:real^3)$1 - (x:real^3)$1):real`;`&2 * ((p:real^3)$1 - (y:real^3)$1):real`] floor_ineq) THEN ASM_REWRITE_TAC[]
		     THEN MP_TAC(SPECL [`&2 * ((p:real^3)$2 - (x:real^3)$2):real`;`&2 * ((p:real^3)$2 - (y:real^3)$2):real`] floor_ineq) THEN ASM_REWRITE_TAC[] THEN MP_TAC(SPECL [`&2 * ((p:real^3)$3 - (x:real^3)$3):real`;`&2 * ((p:real^3)$3 - (y:real^3)$3):real`] floor_ineq) THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_FIELD `&2 * ((a:real) - b) - &2 * (a- c)= &2*(c - b) `] THEN REWRITE_TAC[REAL_ABS_MUL] THEN MP_TAC(SPEC `&2:real` REAL_ABS_REFL) THEN REWRITE_TAC[REAL_ARITH ` &0 <= &2`]
		     THEN SIMP_TAC[] THEN REWRITE_TAC[REAL_ARITH ` &2* a< b <=> a< b/ &2`]
		     THEN REWRITE_TAC[MESON[REAL_ARITH `&1/ &2= abs (&1/ &2)`;REAL_LT_SQUARE_ABS;REAL_ARITH ` (&1/ &2) pow 2 = &1/ &4`] `abs (a:real) < &1/ &2 <=> a pow 2 < &1/ &4`] THEN REPEAT DISCH_TAC THEN SUBGOAL_THEN `norm(y:real^3 - x)< sqrt(&3/ &4)` MP_TAC
THENL [REWRITE_TAC[vector_norm;dist] THEN MP_TAC(SPEC `((y:real^3 - x) dot (y - x)):real` SQRT_POS_LE)
	 THEN REWRITE_TAC[DOT_POS_LE] THEN REWRITE_TAC[REAL_ARITH `&0<= a <=> a= abs a`]
	 THEN REWRITE_TAC[MESON[] `a:real= b ==> a<  sqrt (&3 / &4) <=> a= b ==> b <  sqrt (&3 / &4)`]
	 THEN DISCH_TAC THEN MP_TAC (SPEC `&3 / &4 :real` SQRT_POS_LE) THEN REWRITE_TAC[REAL_ARITH `&0<= &3/ &4`]
	 THEN REWRITE_TAC[REAL_ARITH `&0<= a <=> a= abs a`] THEN REWRITE_TAC[MESON[] `a:real= b ==> c<  a <=> a= b ==> c < b`]
	 THEN SIMP_TAC[REAL_LT_SQUARE_ABS;REAL_ARITH `&1/ &2= abs (&1/ &2)`;MESON[SQRT_POW_2;REAL_ARITH `&0<= &3/ &4`] `(sqrt (&3 / &4))  pow 2= &3/ &4`;SQRT_POW_2;DOT_POS_LE] THEN REWRITE_TAC[DOT_3;DIMINDEX_3] THEN REWRITE_TAC[VECTOR_SUB_COMPONENT;REAL_ARITH `(a:real) * a= a pow 2`] THEN ASM_MESON_TAC[REAL_ARITH `a:real< &1/ &4 /\ b< &1/ &4 /\ c< &1/ &4 ==> a+b+c < &3/ &4`]; DISCH_TAC THEN MP_TAC(MESON[REAL_RAT_REDUCE_CONV `sqrt (&3 / &4) < &2`;REAL_ARITH `a:real<b /\ b< c ==> a< c`] `norm (y:real^3 - x) < sqrt (&3 / &4)/\ sqrt (&3 / &4) < &2 ==> norm (y- x)< &2`)
	   THEN ASM_REWRITE_TAC[bdt_canbatrenbon] THEN UNDISCH_TAC `(packing (S:real^3 -> bool)):bool`
	   THEN REWRITE_TAC[packing] THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`y:real^3`;`x:real^3`]) THEN UNDISCH_TAC `((x:real^3) IN (S:real^3 -> bool) /\ x IN ball (p:real^3,r)):bool`
	   THEN UNDISCH_TAC `((y:real^3) IN (S:real^3 -> bool) /\ y IN ball (p:real^3,r)):bool`
	   THEN SIMP_TAC[SET_RULE `(a:real^3) IN (S:real^3 -> bool ) <=> S a`] THEN REPLICATE_TAC 2 DISCH_TAC
	   THEN REWRITE_TAC[REAL_ARITH `a:real < &2 <=> ~( &2<= a)`]
	   THEN REWRITE_TAC[MESON[] `a ==> b==> c <=> a/\b ==> c`] THEN ONCE_REWRITE_TAC[MESON[] ` ~ (P:bool) ==> Q <=> (~ Q ==> P)`] THEN SIMP_TAC[]]);;


(*-----------------------------------------------------------------*)
(*       Lemma 5.1 [KIUMVTC] Finiteness of packing inter ball      *)
(*-----------------------------------------------------------------*)



let KIUMVTC=prove(`!(p:real^3)(r:real) (S:real^3 -> bool).(&0 <= r) /\ (packing S)  ==> FINITE (S INTER ball(p,r))`,
		  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPECL [`(map3 (p:real^3)):real^3 -> real^3`;`(S INTER ball(p,r)):real^3 ->bool`;`(int_ball (vec 0) (sqrt( &8 * (r pow 2) + &6))):real^3 ->bool`] FINITE_IMAGE_INJ )
		    THEN ASM_SIMP_TAC[map3_define;finite_int_ball;inj_map3]
		    THEN REWRITE_TAC[int_ball;IN_INTER] THEN REWRITE_TAC[hinhcau_ball;IN_ELIM_THM;LAMBDA_BETA;DIMINDEX_3]
		    THEN ASM_SIMP_TAC[map3_define] THEN REWRITE_TAC[map3;IN_ELIM_THM;LAMBDA_BETA;DIMINDEX_3]
		    THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA;DIMINDEX_3] THEN MESON_TAC[FLOOR;GSYM INTEGER_IS_INT]);;

(*-----------------------------------------------------------------*)
(*                      About voronoi cell                         *)
(*-----------------------------------------------------------------*)



let voronoi = new_definition `voronoi v S = { x | !w. ((S w) /\ ~(w=v)) ==> (dist( x, v) < dist( x, w)) }`;;

let bis = new_definition `bis u v = {x | dist(x,u) = dist(x,v)}`;;

let nua_kg=new_definition `nua_kg (u:real^3) (v:real^3) = {x:real^3 | dist(x,u) <  dist(x,v)}`;;

let saturate=new_definition `saturate S= (!x. ?y. y IN S /\ dist (x,y)< &2)`;;

let voronoi_version2=prove( `!(v:real^3) (S:real^3-> bool). voronoi v S = INTERS {nua_kg x y | y IN (S DELETE v)/\ x= v}`,
REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION;GSYM SUBSET_ANTISYM_EQ;voronoi;INTERS]
  THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC
THENL [REWRITE_TAC[SUBSET;IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC
	 THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_ASSUM (MP_TAC o ISPEC `y:real^3`) THEN UNDISCH_TAC `(((y:real^3) IN S DELETE (v:real^3) /\ x' = v) /\ u = nua_kg x' y):bool` THEN REWRITE_TAC[DELETE;IN_ELIM_THM] THEN SIMP_TAC[SET_RULE `y:real^3 IN S <=> S y`] 
THEN REWRITE_TAC[nua_kg;IN_ELIM_THM];REWRITE_TAC[SUBSET;IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC] THEN GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o ISPEC ` (nua_kg (v:real^3) (w:real^3)):real^3 ->bool`) THEN REWRITE_TAC[nua_kg;IN_ELIM_THM] THEN DISCH_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `(?(x:real^3) (y:real^3).
           (y IN S DELETE v /\ x = v) /\
           {x | dist (x,v) < dist (x,w)} = {x' | dist (x',x) < dist (x',y)})` ASSUME_TAC
THENL [EXISTS_TAC `(v):real^3` THEN EXISTS_TAC `w:real^3` THEN 
ASM_REWRITE_TAC[DELETE;IN_ELIM_THM;SET_RULE `w:real^3 IN S <=> S w`];UNDISCH_TAC `((?(x:real^3) (y:real^3).
           (y IN S DELETE v /\ x = (v:real^3)) /\
           {x | dist (x,v) < dist (x,w)} = {x' | dist (x',x) < dist (x',y)})
      ==> dist (x,v) < dist (x,w)):bool` THEN ASM_REWRITE_TAC[]]);;


let norm_ineq_lt= prove(`!(x:real^3)(y:real^3). norm x< norm y <=> x dot x < y dot y`,REPEAT GEN_TAC THEN REWRITE_TAC[MESON[NORM_POS_LE;REAL_ARITH ` &0<=  a <=> a = abs a`] `norm (x:real^3) < norm (y:real^3) <=> abs (norm x) < abs (norm y)`] THEN MESON_TAC[REAL_LT_SQUARE_ABS;NORM_POW_2]);;


let nua_kg_version2=prove(`!(v:real^3)(y:real^3). ?(a:real^3)(b:real). nua_kg v y= { x:real^3 | x dot a < b}`,
REPEAT GEN_TAC THEN EXISTS_TAC `&2 %(y:real^3 - v):real^3` THEN EXISTS_TAC `((y:real^3)$1 * y$1+ y$2 * y$2 + y$3 * y$3 - (v:real^3)$1 * v$1- v$2 * v$2 - v$3 * v$3 ):real` THEN REWRITE_TAC[nua_kg;EXTENSION;IN_ELIM_THM] THEN GEN_TAC
  THEN  REWRITE_TAC[dist;norm_ineq_lt] THEN REWRITE_TAC[DOT_3] THEN ONCE_REWRITE_TAC[REAL_ARITH `a:real < b <=> &0< b - a`]
  THEN REWRITE_TAC[VECTOR_MUL_COMPONENT;VECTOR_SUB_COMPONENT] THEN REWRITE_TAC[REAL_FIELD `(((x:real^3)$1 - (y:real^3)$1) * (x$1 - y$1) +
  (x$2 - y$2) * (x$2 - y$2) +
  (x$3 - y$3) * (x$3 - y$3)) -
 ((x$1 - (v:real^3)$1) * (x$1 - v$1) +
  (x$2 - v$2) * (x$2 - v$2) +
  (x$3 - v$3) * (x$3 - v$3))= (y$1 * y$1 + y$2 * y$2 + y$3 * y$3 - v$1 * v$1 - v$2 * v$2 - v$3 * v$3) -
 (x$1 * &2 * (y$1 - v$1) + x$2 * &2 * (y$2 - v$2) + x$3 * &2 * (y$3 - v$3))`]);;


let convex_nua_kg=prove(`!(v:real^3)(y:real^3).  convex (nua_kg v y)`,REPEAT GEN_TAC THEN MP_TAC(ISPECL [`v:real^3`;`y:real^3`] nua_kg_version2) THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN ASM_SIMP_TAC[]
			   THEN ONCE_REWRITE_TAC[CONVEX_HALFSPACE_LT;DOT_SYM] THEN MESON_TAC[CONVEX_HALFSPACE_LT]);;


(*------------------------------------------------------------*)
(*                     Convexity of Voronoi                   *)
(*------------------------------------------------------------*)



let convex_voronoi=prove( `!(v:real^3) (S:real^3-> bool). convex (voronoi v S)`,REPEAT GEN_TAC THEN MP_TAC(ISPECL [`v:real^3`;`S:real^3 -> bool`] voronoi_version2) THEN SIMP_TAC[] THEN DISCH_TAC THEN SUBGOAL_THEN `! s. s IN {nua_kg (x:real^3) (y:real^3) | y IN S DELETE (v:real^3) /\ x = v} ==> convex s` MP_TAC THENL [GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[convex_nua_kg];MESON_TAC[CONVEX_INTERS]]);;


(*------------------------------------------------------------*)
(*                      Boundness of voronoi                  *)
(*------------------------------------------------------------*)


let bound_voronoi=prove( `!(v:real^3) (S:real^3-> bool). saturate S ==>  bounded(voronoi v S)`,
REPEAT GEN_TAC THEN DISJ_CASES_TAC (MESON[] `bounded (voronoi (v:real^3) (S:real^3 ->bool)) \/ ~(bounded (voronoi v S))`)
  THENL [ASM_MESON_TAC[];UNDISCH_TAC `(~ bounded (voronoi (v:real^3) (S:real^3 ->bool))):bool`
  THEN REWRITE_TAC[bounded] THEN REWRITE_TAC[MESON[] `~(?(a:real). !(x:real^3). x IN voronoi (v:real^3) (S:real^3->bool) 
==> norm x <= a) <=> !(a:real). 
~ (!(x:real^3). x IN voronoi (v:real^3) (S:real^3->bool) ==> norm x <= a)`]
  THEN REWRITE_TAC[MESON[] `~(!x. x IN voronoi (v:real^3) (S:real^3->bool) ==> norm x <= a) 
<=> ? (x:real^3). ~ ( x IN voronoi v S ==> norm x <= a)`] 
THEN REWRITE_TAC[MESON[NOT_IMP] `~((x:real^3) IN voronoi (v:real^3) (S:real^3->bool) ==> norm x <= a) 
<=> x IN voronoi v S /\ ~ (norm x <= a)`]
  THEN REWRITE_TAC[REAL_ARITH ` ~ (norm (x:real^3)<= a:real) <=> a< norm x`]
  THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `norm (v:real^3) + &2:real`)
  THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN UNDISCH_TAC `(x:real^3 
IN voronoi (v:real^3) (S:real^3->bool) /\ norm (v:real^3)+ &2 < norm x):bool` 
THEN REWRITE_TAC[voronoi;saturate;IN_ELIM_THM]
  THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(x):real^3`)
  THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC
  THEN UNDISCH_TAC `(!(w:real^3). S w /\ ~(w = v:real^3) ==> dist (x,v) < dist (x,w)):bool`
 THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`)
  THEN MP_TAC(MESON[REAL_ARITH `norm (v:real^3) + &2 < norm (x:real^3) ==> &2 < norm x - norm v`;
MESON[REAL_ABS_SUB_NORM;REAL_ABS_LE;REAL_ARITH `(a:real)<= b /\ b<= c ==> a<= c`] `norm (x:real^3) - norm (v:real^3)
<= norm (x- v)`;REAL_ARITH `a:real < b /\ b<= c ==> a< c`] `norm (v:real^3) + &2 < norm (x:real^3) ==> &2< norm ( x - v)`)
  THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3 IN (S:real^3 -> bool) /\ dist (x,y) < &2):bool` THEN STRIP_TAC
  THEN REWRITE_TAC[GSYM dist] THEN DISCH_TAC THEN SUBGOAL_THEN `~ (y:real^3 = v)` MP_TAC
THENL [(*1*)DISJ_CASES_TAC(MESON[] `(y:real^3 = v) \/ ~(y=v)`) THENL [UNDISCH_TAC `(dist (x:real^3,y) < &2):bool` 
THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ARITH ` ~ (dist (x:real^3,v) < &2) <=> &2<= dist(x, v)`] 
THEN ASM_MESON_TAC[REAL_ARITH `&2< a ==> &2 <= a`];ASM_MESON_TAC[]];(*2*)ASM_SIMP_TAC[SET_RULE `y:real^3 IN S <=> S y`]
 THEN DISCH_TAC THEN ASM_SIMP_TAC[SET_RULE `y:real^3 IN S <=> S y`] THEN UNDISCH_TAC `(y IN (S:real^3 ->bool)):bool`
 THEN REWRITE_TAC[SET_RULE `y IN (S:real^3 ->bool) <=> S y`] THEN SIMP_TAC[] THEN DISCH_TAC 
THEN UNDISCH_TAC `(dist (x:real^3,y) < &2):bool` THEN UNDISCH_TAC `(&2 < dist (x,v:real^3)):bool` THEN REAL_ARITH_TAC]]);;

(*--------------------------------------------------------------*)


let open_nua_kg=prove(`!(v:real^3)(y:real^3).  open (nua_kg v y)`,REPEAT GEN_TAC THEN MP_TAC(ISPECL [`v:real^3`;`y:real^3`] nua_kg_version2) THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN ASM_SIMP_TAC[]
			   THEN ONCE_REWRITE_TAC[OPEN_HALFSPACE_LT;DOT_SYM] THEN MESON_TAC[OPEN_HALFSPACE_LT]);;



let map_to_nua_kg=new_definition`map_to_nua_kg ((x:real^3), (y:real^3))= nua_kg x y`;;


let surj_map_to_nua_kg=prove(`!(v:real^3)(S:real^3 ->bool). IMAGE (map_to_nua_kg) ({v:real^3} CROSS ((S DELETE v) INTER ball(v, &4))) = {nua_kg (x:real^3) (y:real^3) | (y IN (S DELETE v)) /\ (x = v) /\ (y IN ball(v, &4))}`,
REWRITE_TAC[IMAGE] THEN REWRITE_TAC[map_to_nua_kg] THEN REPEAT GEN_TAC THEN REWRITE_TAC[IN_CROSS;map_to_nua_kg;IN_ELIM_THM] THEN ONCE_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN STRIP_TAC
THENL [(*1*)REWRITE_TAC[SUBSET;IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC
  THEN MP_TAC(ISPEC `x':real^3 # real^3`  PAIR_SURJECTIVE) THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN UNDISCH_TAC `(x':real^3 # real^3 IN {v:real^3} CROSS ((S:real^3 -> bool) DELETE v INTER ball (v,&4)) /\ x = map_to_nua_kg x'):bool` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_CROSS;IN_SING] THEN REWRITE_TAC[map_to_nua_kg;IN_INTER]
  THEN REPEAT STRIP_TAC THEN EXISTS_TAC `x'':real^3` THEN EXISTS_TAC `y:real^3` THEN ASM_SIMP_TAC[];(*2*)REWRITE_TAC[SUBSET;IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN EXISTS_TAC `(x':real^3, y:real^3):real^3 # real^3` THEN ASM_REWRITE_TAC[IN_SING;IN_CROSS;map_to_nua_kg;IN_INTER]]);;



let finite_voronoi2=prove(`!(v:real^3)(S:real^3 ->bool). packing S ==>  FINITE ({nua_kg (x:real^3) (y:real^3) | y IN (S DELETE v)/\ x= v /\ y IN ball(v, &4)})`,REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM surj_map_to_nua_kg]
			    THEN SUBGOAL_THEN `FINITE ({v:real^3} CROSS (S:real^3 ->bool DELETE v INTER ball (v,&4)))` ASSUME_TAC THENL [(*1*)MATCH_MP_TAC FINITE_CROSS THEN SIMP_TAC[FINITE_SING] THEN MATCH_MP_TAC FINITE_SUBSET
			      THEN EXISTS_TAC `((S:real^3->bool) INTER ball(v:real^3, &4)):real^3 ->bool`
																	  THEN REWRITE_TAC[SUBSET_INTER] THEN ASM_MESON_TAC[REAL_ARITH `&0<= &4`;KIUMVTC;SET_RULE `S DELETE v INTER ball (v,&4) SUBSET S /\
 S DELETE v INTER ball (v,&4) SUBSET ball (v,&4)`];(*2*)ASM_MESON_TAC[FINITE_IMAGE]]);;


let real_sub_norm=prove(`!(x:real^3)(y:real^3)(z:real^3). dist (x,z) - dist (y,z)<= dist (x,y)`,
REWRITE_TAC[dist] THEN MESON_TAC[VECTOR_ARITH `x:real^3 - y= (x-z) - (y - z)`;REAL_ABS_SUB_NORM;REAL_ABS_LE;REAL_ARITH `a<= b /\ b<= c ==> a<= c`]);;


let not_open = prove (`!s:real^N->bool. ~ (open s) <=> ?a x. a IN s /\ (!n. ~(x n IN s)) /\ (x --> a) sequentially`,
  REWRITE_TAC[OPEN_CLOSED; CLOSED_LIMPT; LIMPT_SEQUENTIAL] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; IN_DELETE; IN_DIFF; IN_UNIV] THEN
  MESON_TAC[]);;

let not_open_voronoi1 = prove (`!x y v (w:real^N) (A:real^N -> bool). FINITE A /\ (x --> w) sequentially /\ (!n. dist(x n,v) >= dist(x n,y n)) /\ ~(?N. !n. N < n ==> ~(y n IN A)) ==> ?a. a IN A /\ dist(w,v) >= dist(w,a)`, REPEAT GEN_TAC THEN ASM_CASES_TAC `A:real^N->bool = {}` THEN  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN  REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; NOT_IMP] THEN  REPEAT STRIP_TAC THEN  REWRITE_TAC[MESON[] `(?a. P a /\ Q a) <=> ~(!a. P a ==> ~Q a)`] THEN  REWRITE_TAC[real_ge; REAL_NOT_LE] THEN DISCH_TAC THEN  SUBGOAL_THEN   `?e. &0 < e /\ !a. a IN A ==> dist(w:real^N,v) + e <= dist(w,a)`  STRIP_ASSUME_TAC THENL   [EXISTS_TAC `inf(IMAGE (\a:real^N. dist(w,a) - dist(w,v)) A)` THEN ASM_REWRITE_TAC[REAL_ARITH `x + inf s <= y <=> inf s <= y - x`] THEN    ASM_SIMP_TAC[REAL_LT_INF_FINITE; REAL_INF_LE_FINITE; FINITE_IMAGE;IMAGE_EQ_EMPTY] THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE; REAL_SUB_LT] THEN    MESON_TAC[REAL_LE_REFL];    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "*")) THEN    FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` MP_TAC o SPEC `N:num`) THEN    STRIP_TAC THEN REMOVE_THEN "*" (MP_TAC o SPEC `n:num`) THEN    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `(y:num->real^N) n`)) THEN    ASM_SIMP_TAC[LT_IMP_LE] THEN NORM_ARITH_TAC]);;



let not_open_voronoi2 = prove (`!x v w:real^N.(x --> w) sequentially /\(?N. !n. N < n ==> &2 <= dist(x n, v))==> &2 <= dist(w,v)`,  REWRITE_TAC[dist] THEN REPEAT STRIP_TAC THEN  MP_TAC(ISPECL [`sequentially`; `\n. (x:num->real^N) n - v`; `w - v:real^N`; `&2`] LIM_NORM_LBOUND) THEN  ASM_SIMP_TAC[LIM_SUB; LIM_CONST; TRIVIAL_LIMIT_SEQUENTIALLY] THEN  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN  EXISTS_TAC `N + 1` THEN  ASM_REWRITE_TAC[ARITH_RULE `N + 1 <= n <=> N < n`]);;


let not_in_voronoi=prove( `!(x:real^3)(v:real^3)(S:real^3 -> bool). ~ (x IN voronoi v S) <=> ?y. y IN S /\ ~ (y = v) /\ dist (x,y)<= dist (x,v)`,
REWRITE_TAC[voronoi;IN_ELIM_THM] THEN REWRITE_TAC[NOT_FORALL_THM] THEN REWRITE_TAC[NOT_IMP] THEN MESON_TAC[SET_RULE ` y IN S <=> S y`;REAL_ARITH `~ (a< b) <=> b<= a`]);;

let not_open_voronoi3=prove( `!(v:real^3)(S:real^3 -> bool). ~ (open (voronoi v S)) ==> ?x a y. a IN (voronoi v S) /\ (!n. ~ (x n IN (voronoi v S))) /\ (x --> a) sequentially /\ (!n. (y n IN S) /\ ~ (y n = v) /\ dist (x n, y n)<= dist (x n, v))`,
REWRITE_TAC[not_open] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM CHOOSE_TAC
THEN EXISTS_TAC `x:num -> real^3` THEN EXISTS_TAC `a:real^3` THEN ASM_SIMP_TAC[] THEN DISJ_CASES_TAC (MESON[] `( ?y. (!n. (y:num->real^3) n IN (S:real^3 ->bool) /\ ~(y n = v) /\ dist (x n,y n) <= dist (x n,v))) \/ ~ (?y. !n. (y n IN S /\ ~(y n = v) /\ dist (x n,y n) <= dist (x n,v)))`) THENL [(*1*)ASM_MESON_TAC[];(*2*)UNDISCH_TAC `~(?y. (!n. (y:num->real^3) n IN (S:real^3 ->bool) /\ ~(y n = v) /\ dist (x n,y n) <= dist (x n,v))):bool` THEN REWRITE_TAC[NOT_EXISTS_THM;NOT_FORALL_THM] THEN UNDISCH_TAC `((a:real^3) IN voronoi (v:real^3) (S:real^3->bool) /\ (!n. ~((x:num ->real^3) n IN voronoi v S)) /\ (x --> a) sequentially):bool` THEN REWRITE_TAC[not_in_voronoi] THEN MESON_TAC[]]);;


let voronoi_in_ball=prove(`!(x:real^3)(v:real^3)(S:real^3 -> bool).packing S /\ saturate S /\( x IN voronoi v S) ==> dist(x,v)< &2`,REWRITE_TAC[saturate;packing;voronoi;IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN UNDISCH_TAC `(!(x:real^3). ?(y:real^3). y IN (S:real^3 ->bool) /\ dist (x,y) < &2):bool` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN SUBGOAL_THEN `(S:real^3->bool) (y:real^3)` MP_TAC
THENL [(*1*)ASM_MESON_TAC[SET_RULE `(y:real^3) IN (S:real^3 -> bool) ==> S y`];(*2*)DISCH_TAC THEN UNDISCH_TAC `(!(w:real^3). (S:real^3->bool) w /\ ~(w = v) ==> dist (x:real^3,v) < dist (x,w)):bool` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN DISJ_CASES_TAC (MESON[] ` (y:real^3 = v) \/ ~ (y = v)`) THENL [(*2a*)ASM_MESON_TAC[];(*2b*)ASM_SIMP_TAC[]
	 THEN UNDISCH_TAC `((y:real^3) IN (S:real^3->bool) /\ dist (x:real^3,y) < &2):bool` THEN STRIP_TAC THEN ASM_MESON_TAC[REAL_ARITH `a<b /\ b< c ==> a< c`]]]);;




(*----------------------------------------------------------------*)
(*                           Openness                             *)
(*----------------------------------------------------------------*)


let open_voronoi=prove( `!(v:real^3)(S:real^3 -> bool).packing S /\ saturate S ==> open (voronoi v S)`,REPEAT STRIP_TAC THEN DISJ_CASES_TAC (MESON[] ` open (voronoi (v:real^3) (S:real^3 ->bool)) \/ ~ (open (voronoi v S))`) THENL [(*1*)ASM_MESON_TAC[];(*2*)MP_TAC(ISPECL [`v:real^3`;`S:real^3 -> bool`] not_open_voronoi3) THEN ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[MESON[] `~ p <=> p ==> F`] THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM CHOOSE_TAC
			  THEN UNDISCH_TAC `((a:real^3) IN voronoi (v:real^3) (S:real^3->bool) /\
      (!n. ~((x:num ->real^3) n IN voronoi v S)) /\
      (x --> a) sequentially /\
      (!n. (y:num -> real^3) n IN S /\ ~(y n = v) /\ dist (x n,y n) <= dist (x n,v))):bool` THEN REPEAT STRIP_TAC
			    THEN DISJ_CASES_TAC(MESON[] `(?(N:num). !n. N< n ==> ~((y:num -> real^3) n IN ball(v, &4))) \/ ~ (?N. !n. N< n ==> ~(y n IN ball(v, &4)))`) THENL [(*2a*)UNDISCH_TAC `( (?(N:num). !n. N< n ==> ~((y:num -> real^3) n IN ball(v, &4)))):bool` THEN REWRITE_TAC[ball;IN_ELIM_THM] THEN REWRITE_TAC[REAL_ARITH ` ~ (a:real< b) <=> b<= a`] THEN STRIP_TAC
			      THEN SUBGOAL_THEN `!(n:num). N< n ==> &2 <= dist((x:num -> real^3) n,v)` MP_TAC 
THENL [(*2a1*)REPEAT STRIP_TAC THEN MP_TAC(MESON[DIST_SYM] `dist ((x:num->real^3) n,(y:num -> real^3) n) <= dist (x n,v:real^3) ==> dist(x n, y n) <= dist (v, x n)`) THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(!(n:num). N < n ==> &4 <= dist (v:real^3,(y:num -> real^3) n)):bool` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[]
  THEN MESON_TAC[REAL_ARITH `a:real <= b ==>  (a+ b) <= &2* b`; DIST_TRIANGLE;REAL_ARITH `a<= b /\ b<= c ==> a<= c`;DIST_SYM;REAL_ARITH `&4<= &2* a <=> &2<= a`];(*2a2*)DISCH_TAC THEN MP_TAC(MESON[] `(!(n:num). (N:num) < n ==> &2 <= dist ((x:num -> real^3) n,v:real^3)) ==> (? (M:num). (!(n:num). M < n ==> &2 <= dist (x n,v)))`) THEN ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[MESON[] `~ p <=> p ==> F`] THEN DISCH_TAC THEN MP_TAC(ISPECL [`x:num ->real^3`;`v:real^3`;`a:real^3`] not_open_voronoi2) 
  THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[REAL_ARITH `~ (a<= b ) <=> b< a`] THEN ASM_MESON_TAC[voronoi_in_ball]];(*2b*)MP_TAC(ISPECL [`x:num ->real^3`;`y:num -> real^3`;`v:real^3`;`a:real^3`;`(((S:real^3 ->bool) INTER ball(v:real^3, &4)) DELETE v):real^3 -> bool`] not_open_voronoi1) THEN ASM_REWRITE_TAC[IN_INTER;REAL_ARITH `a:real >= b <=> b<= a`] THEN REWRITE_TAC[IN_DELETE] THEN ASM_SIMP_TAC[IN_INTER] THEN MP_TAC(ISPECL [`v:real^3`;` &4:real`;`S:real^3 ->bool`] KIUMVTC ) THEN ASM_REWRITE_TAC[REAL_ARITH `&0<= &4`;DELETE_SUBSET;FINITE_SUBSET]  THEN DISCH_TAC THEN MP_TAC (MESON[DELETE_SUBSET;FINITE_SUBSET] ` (FINITE ((S:real^3->bool) INTER ball (v:real^3,&4))) ==> (FINITE ((S INTER ball (v,&4)) DELETE v))`) THEN ASM_REWRITE_TAC[]
			      THEN UNDISCH_TAC `((a:real^3) IN voronoi (v:real^3) (S:real^3 -> bool)):bool` THEN REWRITE_TAC[voronoi;IN_ELIM_THM] THEN REWRITE_TAC[NOT_IMP] THEN SIMP_TAC[NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN UNDISCH_TAC ` (!(w:real^3). (S:real^3 ->bool) w /\ ~(w = v) ==> dist (a:real^3,v) < dist (a,w)):bool` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `a':real^3`) THEN ASM_MESON_TAC[SET_RULE `(a':real^3) IN (S:real^3 -> bool) <=> S a'`;REAL_ARITH ` a:real <= b <=> ~ (b< a)`]]]);;


(*----------------------------------------------------------------*)
(*     Lemma 5.2 [DRUQUFE]About voronoi, this is not element      *)
(*----------------------------------------------------------------*)


let DRUQUFE=prove(`!(v:real^3)(S:real^3 -> bool).packing S /\ saturate S ==> convex (voronoi v S) /\ bounded (voronoi v S) /\ open (voronoi v S) /\ measurable ( voronoi v S)`,MESON_TAC[convex_voronoi;bound_voronoi;open_voronoi;MEASURABLE_OPEN]);;

(*----------------------------------------------------------------*)
(*             The following is to prove Lemma 5.3                *)
(*----------------------------------------------------------------*)


let measurable_voronoi=prove(`!(v:real^3)(S:real^3 -> bool).packing S /\ saturate S ==> measurable ( voronoi v S)`, MESON_TAC[DRUQUFE]);;

   let negligible_fun = new_definition `negligible_fun f S = (? (C:real). (&0<= C)/\ ! (r:real) (p:real^3). ( &1 <= r) ==> (sum (S INTER ball(p,r)) f) <= C * (r pow 2))`;;

   let fcc_compatible= new_definition `fcc_compatible f S = (!v. v IN S ==> sqrt( &32) <= measure(voronoi v S) + f v)`;;


   let packing_subset_unions_ball=prove( `! (S:real^3 ->bool) (p:real^3) (r:real). ((UNIONS {ball(v:real^3, &1) | v IN S}) INTER ball(p,r)) SUBSET UNIONS {ball(v:real^3, &1) | v IN (S INTER ball (p,r+ &1))}`,REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET;IN_INTER;UNIONS] THEN GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `ball(v:real^3, &1):real^3 ->bool` THEN STRIP_TAC THENL [(*1*)EXISTS_TAC `(v):real^3` THEN ASM_SIMP_TAC[] THEN UNDISCH_TAC `(x:real^3 IN u):bool`
					   THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x IN ball (p:real^3,r)):bool` THEN REWRITE_TAC[ball;IN_ELIM_THM] THEN REWRITE_TAC[dist] THEN REWRITE_TAC[MESON[VECTOR_ARITH `(p:real^3- x) + (x- v)= p - v`] `norm (p:real^3 - v) < r + &1 <=> norm ((p- x) + (x- v))< r+ &1`] THEN MESON_TAC[NORM_SUB;NORM_TRIANGLE;REAL_ARITH `a<d /\ b<c/\ e<= a+ b ==> e< d+ c`]; (*2*)ASM_MESON_TAC[SET_RULE `u = ball(v:real^3, &1):real^3 ->bool /\ x IN u ==> (x:real^3) IN ball (v,&1)`]]);;


let measurable_packing_lm1=prove(`! (S:real^3 ->bool) (p:real^3) (r:real). measurable((UNIONS {ball(v:real^3, &1) | v IN S}) INTER ball(p,r))`,let em=CONJUNCT2 INTER_SUBSET in REPEAT GEN_TAC THEN MATCH_MP_TAC (ISPEC `(UNIONS {ball(v:real^3, &1) | v IN S} INTER ball(p,r)):real^3 ->bool` MEASURABLE_OPEN) THEN STRIP_TAC THENL [(*1*)MESON_TAC[BOUNDED_SUBSET;em;BOUNDED_BALL];(*2*)MATCH_MP_TAC OPEN_INTER THEN SIMP_TAC[OPEN_BALL] THEN MATCH_MP_TAC OPEN_UNIONS THEN GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[OPEN_BALL]]);;


let map_to_ball=new_definition`map_to_ball (x:real^3)= ball(x, &1)`;;


let surj_map_to_ball=prove(`!(S:real^3 ->bool). IMAGE (map_to_ball) S = {ball(x:real^3, &1) | x IN S}`,
REWRITE_TAC[IMAGE] THEN REWRITE_TAC[map_to_ball] THEN REPEAT GEN_TAC THEN REWRITE_TAC[map_to_ball;IN_ELIM_THM] THEN ONCE_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN STRIP_TAC
THENL [(*1*)REWRITE_TAC[SUBSET;IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC;(*2*)REWRITE_TAC[SUBSET;IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC]);;

let finite_set_packing_in_ball=prove(`! (S:real^3 ->bool) (p:real^3) (r:real). &0<= r /\ packing S ==>  FINITE ({ball(v:real^3, &1) | v IN (S INTER ball (p,r+ &1))})`,REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM surj_map_to_ball]
				       THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC[KIUMVTC;REAL_ARITH `&0<= r ==> &0<= r+ &1`]);;


let measurable_packing_lm2=prove(`! (S:real^3 ->bool) (p:real^3) (r:real). &0<= r /\packing S ==> measurable (UNIONS {ball(v:real^3, &1) | v IN (S INTER ball (p,r+ &1))})`, REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_UNIONS
				  THEN ASM_SIMP_TAC[finite_set_packing_in_ball] THEN GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM;MEASURABLE_BALL] THEN MESON_TAC[MEASURABLE_BALL]);;


let measure_ineq_lm53_1=prove( `! (S:real^3 ->bool) (p:real^3) (r:real). &0<= r /\packing S ==> measure ((UNIONS {ball(v:real^3, &1) | v IN S}) INTER ball(p,r)) <= measure(UNIONS {ball(v:real^3, &1) | v IN (S INTER ball (p,r+ &1))})`,MESON_TAC[MEASURE_SUBSET;packing_subset_unions_ball;measurable_packing_lm1;measurable_packing_lm2]);;

(*--------------------*)
(*        Step 1      *)
(*--------------------*)

let measure_ineq_lm53_2=prove(`! (S:real^3 ->bool) (p:real^3) (r:real). &0<= r /\packing S ==> measure ((UNIONS {ball(v:real^3, &1) | v IN S}) INTER ball(p,r)) <= & (CARD {ball(v:real^3, &1) | v IN (S INTER ball (p,r+ &1))}) * &4*pi/ &3`,
REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`S:real^3 ->bool`;`p:real^3`;`r:real`] measure_ineq_lm53_1)
  THEN ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `measure (UNIONS {ball (v,&1) | v IN (S:real^3 ->bool) INTER ball (p:real^3,r + &1)}) <= &(CARD {ball (v,&1) | v IN S INTER ball (p,r + &1)}) * &4 * pi / &3` (fun th -> MESON_TAC[th;REAL_ARITH `a<=b /\b <= c ==> a<= c`]) THEN MP_TAC(ISPEC `{ball (v,&1) | v IN (S:real^3 ->bool) INTER ball (p:real^3,r + &1)}` MEASURE_UNIONS_LE)
  THEN ASM_SIMP_TAC[finite_set_packing_in_ball]
  THEN SUBGOAL_THEN `(!(s:real^3 ->bool).s IN {ball (v,&1) | v IN (S:real^3 ->bool) INTER ball (p:real^3,r + &1)} ==> measurable s )` (fun thm -> SIMP_TAC[thm;MEASURABLE_BALL])
THENL [(*1*)GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM;MEASURABLE_BALL] THEN MESON_TAC[MEASURABLE_BALL];(*2*)SUBGOAL_THEN `sum {ball (v,&1) | v IN (S:real^3 ->bool) INTER ball (p:real^3,r + &1)} (\s. measure s)= sum {ball (v,&1) | v IN (S:real^3 ->bool) INTER ball (p:real^3,r + &1)} (\s. &4 * pi/ &3)` MP_TAC THENL [(*2a*)MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN ASM_REWRITE_TAC[] THEN MESON_TAC[VOLUME_BALL;REAL_ARITH `&0<= &1`;REAL_FIELD `&4* pi/ &3 = &4 / &3 * pi * ( &1 pow 3)`];(*2b*)SIMP_TAC[] THEN SUBGOAL_THEN `sum {ball (v:real^3,&1) | v IN (S:real^3 -> bool) INTER ball (p:real^3,r + &1)} (\s. &4 * pi / &3)= &(CARD {ball (v,&1) | v IN (S:real^3 ->bool) INTER ball (p:real^3,r + &1)}) * &4 * pi / &3` (fun th -> SIMP_TAC[th]) THEN MP_TAC(ISPECL [`&4 * pi / &3:real`;`{ball (v,&1) | v IN (S:real^3 ->bool) INTER ball (p:real^3,r + &1)}:(real^3 -> bool) -> bool`] SUM_CONST) THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[finite_set_packing_in_ball;REAL_ARITH `&0<= r ==> &0 <= r+ &1`]]]);;


let card_eq_ball_point=prove( `! (S:real^3 ->bool) (p:real^3) (r:real). &0<= r /\packing S ==> CARD {ball(v:real^3, &1) | v IN (S INTER ball (p,r+ &1))}= CARD(S INTER ball (p,r+ &1))`,REPEAT STRIP_TAC THEN SIMP_TAC[GSYM surj_map_to_ball] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_SIMP_TAC[KIUMVTC;REAL_ARITH `&0<= r ==> &0<= r+ &1`] THEN REPEAT GEN_TAC THEN REWRITE_TAC[map_to_ball;IN_INTER] THEN REPEAT STRIP_TAC THEN UNDISCH_TAC `(packing(S:real^3 ->bool)):bool` THEN REWRITE_TAC[packing] THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^3`;`y:real^3`]) THEN ASM_REWRITE_TAC[IN_INTER;SET_RULE ` (z:real^3) IN (S:real^3 ->bool) <=> S z`] THEN ASM_SIMP_TAC[SET_RULE ` (z:real^3) IN (S:real^3 ->bool) ==> S z`] THEN FIRST_X_ASSUM(fun th -> MP_TAC(th)) THEN REWRITE_TAC[EXTENSION] THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN REWRITE_TAC[ball;IN_ELIM_THM;VECTOR_ARITH `x:real^3 - x = vec 0`] THEN REWRITE_TAC[DIST_REFL;REAL_ARITH ` &0< &1`] THEN MESON_TAC[DIST_SYM;REAL_ARITH `a< &1 ==> ~ (&2<= a)`]);;



(*------------------------------------------------------------------------------------------------------*)
(*Some results involving in set of balls or set of voronoi cells (finiteness,being image of another set)*)
(*------------------------------------------------------------------------------------------------------*)


let voronoi_subset_ball=prove( `!(x:real^3)(v:real^3)(S:real^3 -> bool).packing S /\ saturate S ==> (voronoi v S) SUBSET ball(v, &2)`, REWRITE_TAC[SUBSET;ball] THEN REWRITE_TAC[voronoi_in_ball;IN_ELIM_THM] THEN MESON_TAC[voronoi_in_ball;DIST_SYM]);;


let all_voronoi_subset_ball=prove(`!(v:real^3)(S:real^3 ->bool)(p:real^3)(r:real). packing S /\ saturate S /\ v IN ball(p, r+ &1) ==> (voronoi v S) SUBSET ball(p, r+ &3) `, REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE `voronoi (v:real^3)(S:real^3 -> bool) SUBSET ball(v:real^3, &2) /\ ball(v:real^3, &2 ) SUBSET ball(p:real^3, r+ &3) ==> voronoi v S SUBSET ball (p,r + &3)`) THEN ASM_SIMP_TAC[ voronoi_subset_ball] THEN UNDISCH_TAC `((v:real^3) IN ball (p:real^3,r + &1)):bool` THEN REWRITE_TAC[ball;SUBSET;IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`p:real^3`;`v:real^3`;`x:real^3`] DIST_TRIANGLE) THEN ASM_MESON_TAC[REAL_ARITH ` a< (r:real) + &1 /\ b< &2 /\ c <= a + b ==> c< r + &3`]);;


let unions_voronoi_subset_ball=prove( `!(S:real^3 ->bool)(p:real^3)(r:real). packing S /\ saturate S ==> UNIONS {voronoi v S | v IN ball(p, r+ &1)} SUBSET ball(p, r+ &3)`, REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET;UNIONS;IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN UNDISCH_TAC `((?(v:real^3). v IN ball (p:real^3,r + &1) /\ u = voronoi v (S:real^3 ->bool)) /\ (x:real^3) IN u):bool`
					THEN REPEAT STRIP_TAC THEN UNDISCH_TAC `(x:real^3 IN u:real^3 ->bool):bool` THEN ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`v:real^3`;`S:real^3 ->bool`;`p:real^3`;`r:real`] all_voronoi_subset_ball) THEN ASM_SIMP_TAC[] THEN SET_TAC[]);;

let unions_voronoi_center_in_ball_subset_ball=prove( `!(S:real^3 ->bool)(p:real^3)(r:real). packing S /\ saturate S ==> UNIONS {voronoi v w | v IN (S INTER ball(p, r+ &1)) /\ w = S} SUBSET ball(p, r+ &3)`,REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET;UNIONS;IN_ELIM_THM] THEN GEN_TAC THEN REPEAT STRIP_TAC THEN UNDISCH_TAC `(x:real^3 IN u:real^3 ->bool):bool` THEN ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`v:real^3`;`S:real^3 ->bool`;`p:real^3`;`r:real`] all_voronoi_subset_ball) THEN ASM_SIMP_TAC[] THEN SET_TAC[]);;


let map_to_voronoi=new_definition`map_to_voronoi ((x:real^3), (S:real^3 -> bool))= voronoi x S`;;


let surj_map_to_voronoi=prove(`!(M:real^3 ->bool)(S:real^3 ->bool). IMAGE (map_to_voronoi) (M CROSS {S}) = {voronoi v S | v IN M}`,REWRITE_TAC[IMAGE] THEN REWRITE_TAC[map_to_voronoi] THEN REPEAT GEN_TAC THEN REWRITE_TAC[IN_CROSS;map_to_voronoi;IN_ELIM_THM] THEN ONCE_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN STRIP_TAC THENL [(*1*) REWRITE_TAC[SUBSET;IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN MP_TAC(ISPEC `x':real^3 # (real^3->bool)`  PAIR_SURJECTIVE) THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN UNDISCH_TAC `(x':real^3 # (real^3 -> bool) IN ((M:real^3 ->bool) CROSS {S:real^3 -> bool}) /\ x = map_to_voronoi x'):bool` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_CROSS;IN_SING] THEN REWRITE_TAC[map_to_voronoi;IN_INTER] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `x'':real^3` THEN ASM_SIMP_TAC[];(*2*)REWRITE_TAC[SUBSET;IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN EXISTS_TAC `(v:real^3, S:real^3->bool):real^3 # (real^3 ->bool)` THEN ASM_REWRITE_TAC[IN_SING;IN_CROSS;map_to_voronoi;IN_INTER]]);;

let surj_map_to_voronoi_db=prove( `! (S:real^3 ->bool) (p:real^3) (r:real). IMAGE (map_to_voronoi) ((S INTER ball (p,r + &1)) CROSS {S})= {voronoi v w | v IN (S INTER ball (p,r+ &1)) /\ w = S}`, REWRITE_TAC[IMAGE] THEN REWRITE_TAC[map_to_voronoi] THEN REPEAT GEN_TAC THEN REWRITE_TAC[IN_CROSS;map_to_voronoi;IN_ELIM_THM] THEN ONCE_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN STRIP_TAC THENL [(*1*)REWRITE_TAC[SUBSET;IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN MP_TAC(ISPEC `x':real^3 # (real^3->bool)`  PAIR_SURJECTIVE) THEN STRIP_TAC THEN UNDISCH_TAC `(x':real^3 # (real^3 -> bool) IN ((S:real^3 ->bool INTER ball (p:real^3,r + &1)) CROSS {S:real^3 -> bool}) /\ x = map_to_voronoi x'):bool` THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_CROSS;IN_SING] THEN REWRITE_TAC[map_to_voronoi;IN_INTER] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `x'':real^3` THEN EXISTS_TAC `y:real^3 ->bool` THEN ASM_SIMP_TAC[];(*2*) REWRITE_TAC[SUBSET;IN_ELIM_THM] THEN GEN_TAC THEN REPEAT STRIP_TAC THEN EXISTS_TAC `(v, w):real^3 # (real^3 ->bool)` THEN ASM_REWRITE_TAC[IN_SING;IN_CROSS;map_to_voronoi;IN_INTER]]);;



let finite_set_voronoi_center_in_ball=prove(`! (S:real^3 ->bool) (p:real^3) (r:real). &0<= r /\ packing S ==>  FINITE ({voronoi v w | v IN (S INTER ball (p,r+ &1)) /\ w= S})`, REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM surj_map_to_voronoi_db] THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC[KIUMVTC;FINITE_CROSS;FINITE_SING;REAL_ARITH `&0<= r ==> &0<= r+ &1`]);;



let measurable_unions_voronoi=prove(`! (S:real^3 ->bool) (p:real^3) (r:real). &0<= r /\packing S /\ saturate S==> measurable (UNIONS {voronoi v w | v IN (S INTER ball (p,r+ &1)) /\ w = S})`, REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_UNIONS THEN ASM_SIMP_TAC[finite_set_voronoi_center_in_ball] THEN GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[measurable_voronoi]);;

let negligible_voronoi=prove( `!(S:real^3 ->bool)(p:real^3)(r:real). (!s t.
       s IN {voronoi v w | v IN S INTER ball (p,r + &1) /\ w = S} /\
       t IN {voronoi v w | v IN S INTER ball (p,r + &1) /\ w = S} /\
       ~(s = t)
       ==> negligible (s INTER t))`,REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC (MESON[NEGLIGIBLE_EMPTY] `(s:real^3->bool) INTER (t:real^3 ->bool) = {} ==> negligible (s INTER t)`) THEN ASM_REWRITE_TAC[] THEN SUBGOAL_THEN ` ~ (v:real^3 = v')` MP_TAC 
THENL [(*1*)UNDISCH_TAC `( ~(s:real^3 ->bool = t)):bool` THEN REWRITE_TAC[MESON[] ` ~ p ==> ~q <=> q ==> p`] THEN ASM_MESON_TAC[];(*2*)DISCH_TAC THEN ASM_CASES_TAC `?(x:real^3). x IN (voronoi (v:real^3) (S:real^3 ->bool) INTER voronoi (v':real^3) S)` THEN ASM_REWRITE_TAC[SET_RULE `(B:real^3 -> bool)= {} <=> ~ (?(x:real^3). x IN B)`] THEN FIRST_X_ASSUM CHOOSE_TAC THEN UNDISCH_TAC `((x:real^3) IN (voronoi (v:real^3) (S:real^3 ->bool) INTER voronoi (v':real^3) S)):bool` THEN REWRITE_TAC[voronoi] THEN REWRITE_TAC[IN_INTER;IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `v:real^3`) THEN FIRST_X_ASSUM(MP_TAC o SPEC `v':real^3`) THEN ASM_SIMP_TAC[MESON[] `e=f <=> f=e`;SET_RULE `(v':real^3) IN (S:real^3 ->bool) INTER  ball (p:real^3,r + &1) ==> S v'`] THEN MP_TAC(SET_RULE `(v':real^3) IN (S:real^3 ->bool) INTER  ball (p:real^3,r + &1) ==> S v'`) THEN ASM_SIMP_TAC[] THEN MP_TAC(SET_RULE `(v:real^3) IN (S:real^3 ->bool) INTER  ball (p:real^3,r + &1) ==> S v`) THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC]);;

let inj_map_to_voronoi=prove( `!(S:real^3 ->bool)(p:real^3)(r:real) (x:real^3 # (real^3 -> bool)) (y:real^3 # (real^3 -> bool)).
       x IN ((S INTER ball (p,r + &1)) CROSS {S}) /\
       y IN (S INTER ball (p,r + &1)) CROSS {S} /\
       map_to_voronoi x = map_to_voronoi y
       ==> x = y`,REPEAT GEN_TAC THEN MP_TAC(ISPEC `x:real^3 # (real^3->bool)`  PAIR_SURJECTIVE) THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN ASM_SIMP_TAC[] THEN MP_TAC(ISPEC `y:real^3 # (real^3->bool)`  PAIR_SURJECTIVE) THEN  DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_CROSS;IN_SING] THEN SIMP_TAC[map_to_voronoi]
 THEN REWRITE_TAC[PAIR_EQ] THEN REWRITE_TAC[IN_INTER] THEN REPEAT STRIP_TAC THEN UNDISCH_TAC `(voronoi (x':real^3) (y':real^3->bool) = voronoi (x'':real^3) (y'':real^3->bool)):bool` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN 
SUBGOAL_THEN `x':real^3 IN voronoi x' (S:real^3 ->bool)` MP_TAC THENL [(*1*)REWRITE_TAC[voronoi;IN_ELIM_THM] 
THEN REWRITE_TAC[DIST_REFL] THEN REWRITE_TAC[GSYM DIST_NZ] THEN MESON_TAC[];(*2*)ASM_REWRITE_TAC[] THEN  
REWRITE_TAC[voronoi;IN_ELIM_THM] THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x':real^3`) THEN ASM_SIMP_TAC[DIST_REFL;SET_RULE `(x':real^3) IN (S:real^3 ->bool) ==> S x'`] THEN REWRITE_TAC[REAL_ARITH `dist(x':real^3,x'':real^3) < &0 <=> ~ (&0<= dist (x',x''))`] THEN MESON_TAC[DIST_POS_LE]]);;


let measure_unions_sum_voronoi=prove( `!(S:real^3 ->bool)(p:real^3)(r:real). &0<= r/\ packing S /\ saturate S ==> measure(UNIONS {voronoi v w | v IN (S INTER ball(p, r+ &1)) /\ w = S})= sum (S INTER ball(p, r+ &1)) (\v. measure (voronoi v S))`,
REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`\s:real^3->bool. measure s`;`{voronoi v w | v IN (S:real^3 ->bool INTER ball(p:real^3, r+ &1)) /\ w = S}`] MEASURE_NEGLIGIBLE_UNIONS) THEN REWRITE_TAC[negligible_voronoi] THEN ASM_SIMP_TAC[finite_set_voronoi_center_in_ball;IN_ELIM_THM;measurable_voronoi;HAS_MEASURE_MEASURE] THEN MP_TAC(MESON[HAS_MEASURE_MEASURE;measurable_voronoi] `&0<= r/\ packing (S:real^3 ->bool) /\ saturate S ==> (!(s:real^3 ->bool). (?(v:real^3) (w:real^3->bool). (v IN S INTER ball (p:real^3,r + &1) /\ w = S) /\ s = voronoi v w) ==> s has_measure (measure s))`) THEN ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC
  THEN REWRITE_TAC[GSYM surj_map_to_voronoi_db] THEN MP_TAC(ISPECL [`map_to_voronoi:real^3#(real^3->bool)->real^3->bool`;`(\s:real^3->bool. measure s):(real^3-> bool) -> real`;`(((S:real^3 ->bool) INTER ball (p:real^3,r + &1)) CROSS {S}):real^3#(real^3->bool)->bool`] SUM_IMAGE) THEN REWRITE_TAC[inj_map_to_voronoi] THEN SIMP_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC SUM_EQ_GENERAL THEN EXISTS_TAC `FST:real^3# (real^3 ->bool) -> real^3` THEN REPEAT STRIP_TAC THENL [(*1*)REWRITE_TAC[EXISTS_UNIQUE] THEN EXISTS_TAC `(y:real^3,S:real^3->bool):real^3 # (real^3 ->bool)` THEN ASM_REWRITE_TAC[IN_CROSS;IN_SING;FST] THEN GEN_TAC THEN MP_TAC(ISPEC `y':real^3 # (real^3 ->bool)` PAIR_SURJECTIVE) THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_CROSS;IN_SING] THEN MESON_TAC[];(*2*)UNDISCH_TAC `(x:real^3 # (real^3 ->bool) IN (S:real^3 ->bool INTER ball (p:real^3,r + &1)) CROSS {S}):bool` THEN MP_TAC(ISPEC `x:real^3 # (real^3 ->bool)` PAIR_SURJECTIVE) THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN ASM_REWRITE_TAC[]
    THEN REWRITE_TAC[IN_CROSS] THEN MESON_TAC[];(*3*)MP_TAC(ISPEC `x:real^3 # (real^3 ->bool)` PAIR_SURJECTIVE) THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[map_to_voronoi;IN_CROSS;IN_SING]]);;



(*------------------------*)
(*      Step 2            *)
(*------------------------*)

let sum_measure_voronoi_le_ball=prove( `!(S:real^3 ->bool)(p:real^3)(r:real). &0<= r/\ packing S /\ saturate S ==> sum (S INTER ball (p,r + &1)) (\v. measure (voronoi v S)) <= measure (ball(p,r+ &3))`, REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM measure_unions_sum_voronoi] THEN ASM_MESON_TAC[MEASURE_SUBSET;measurable_unions_voronoi; unions_voronoi_center_in_ball_subset_ball;MEASURABLE_BALL;REAL_ARITH `&0<= r ==> &0<= r+ &3`]);;

(*------------------------*)
(*        Step 3          *)
(*------------------------*)

let ineq_lm5_3_step3=prove(`!(S:real^3 ->bool)(p:real^3)(r:real)(A:real^3 ->real). &0<= r/\ packing S /\ saturate S /\ (fcc_compatible A S)==> sqrt( &32) * &(CARD(S INTER ball (p,r + &1))) <= sum (S INTER ball (p,r + &1)) (\v. (A v + measure (voronoi v S)))`,REWRITE_TAC[fcc_compatible] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN ` sum ((S:real^3 ->bool) INTER ball (p:real^3,r + &1)) (\v. sqrt( &32))<= sum (S INTER ball (p,r + &1)) (\v. A v + measure (voronoi v S)) ` MP_TAC 
THENL [(*1*)MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[KIUMVTC;REAL_ARITH `&0<= r ==> &0<= r + &1`] THEN ASM_MESON_TAC[fcc_compatible;REAL_ARITH `a+b= b+a`;SET_RULE `x IN A INTER B ==> x IN A`];(*2*)ASM_SIMP_TAC[SUM_CONST;KIUMVTC;REAL_ARITH `&0<= r ==> &0<= r + &1`] THEN REAL_ARITH_TAC]);;


(*------------------------*)
(*          Step 4        *)
(*------------------------*)


let ineq_lm5_3_step4=prove(`!(c:real). (&0<= c) ==> ? (c':real). !(r:real). (&1 <=r) ==> ( pi/ sqrt( &18)*( &1+ &3/ r) pow 3 + c*((r+ &1) pow 2)/ (r pow 3 * sqrt( &32)) <= pi/ sqrt( &18) + c'/r)`,REPEAT STRIP_TAC THEN  EXISTS_TAC `((pi/ sqrt( &18))* ( &9+ &27+ &27) + c* (&1/ sqrt( &32) + &2/  sqrt( &32)+ &1/  sqrt( &32))):real` THEN REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REAL_ARITH `a:real<= b <=> &0<= b-a`] THEN ASM_SIMP_TAC[REAL_FIELD ` &1<= r==>(pi / sqrt (&18) +
  (pi / sqrt (&18) * (&9 + &27 + &27) +
   (c:real) * (&1 / sqrt (&32) + &2 / sqrt (&32) + &1 / sqrt (&32))) /
  (r:real)) -
 (pi / sqrt (&18) * ((&1 + &3 / r) pow 3) +
  c * (r + &1) pow 2 / (r pow 3 * sqrt (&32))) =( (&1/ r) * pi/ sqrt( &18)) * ( (&27/r)*( r- &1)+ ( &27/(r pow 2)) * (r pow 2 - &1)) + ( (&1/ r)*c)* (( &2/(r* sqrt( &32)))*(r- &1) + (&1/ (r pow 2 * sqrt( &32))) * (r pow 2 - &1))`]
			     THEN REWRITE_TAC[REAL_FIELD `(&1 / (r:real) * pi / sqrt (&18)) *
 (&27 / r * (r - &1) + &27 / r pow 2 * (r pow 2 - &1)) +
 (&1 / r * (c:real)) *
 (&2 / (r * sqrt (&32)) * (r - &1) +
  &1 / (r pow 2 * sqrt (&32)) * (r pow 2 - &1))= (&1 / r * pi / sqrt (&18)) *
 (&27 / r * (r - &1) + (&27 / r pow 2) * (r - &1) *(r + &1)) +
 (&1 / r * c) *
 (&2 / (r * sqrt (&32)) * (r - &1) +
  &1 / (r pow 2 * sqrt (&32)) * (r - &1)*(r + &1))`] THEN MP_TAC(PI_POS_LE) THEN MP_TAC(REAL_ARITH `&1<= r:real ==> &0<= r- &1`) THEN ASM_REWRITE_TAC[] THEN MP_TAC(REAL_ARITH `&1<= r:real ==> &0<= r+ &1`) THEN ASM_REWRITE_TAC[] THEN MP_TAC(MESON[REAL_ARITH `&0<= &18 /\ &0<= &32`;SQRT_POS_LE] `&0<= sqrt( &18) /\ &0<= sqrt( &32)`) THEN MP_TAC(REAL_ARITH `&1<= r:real ==> &0<=r `) THEN ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `r:real` REAL_LE_SQUARE) THEN REWRITE_TAC[REAL_ARITH ` r * r:real = r pow 2`] THEN MP_TAC(REAL_ARITH ` &0<= &1 /\ &0<= &27 /\ &0<= &2`) THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC (SPECL [`(&1 / (r:real) * pi / sqrt (&18)) *
     (&27 / r * (r - &1) + &27 / r pow 2 * (r - &1) * (r + &1)):real`;`(&1 / r * (c:real)) *
     (&2 / (r * sqrt (&32)) * (r - &1) +
      &1 / (r pow 2 * sqrt (&32)) * (r - &1) * (r + &1)):real`] REAL_LE_ADD) THEN MP_TAC(MESON[REAL_LE_DIV;REAL_ARITH `&0<= &1`;REAL_LE_MUL;REAL_LE_ADD;REAL_ARITH ` a:real <= b /\ b<= c ==> a<= c`] `&0<= r /\ &0 <= pi /\ &0 <= sqrt (&18) ==>  &0<= &1 / r * pi / sqrt (&18)`) THEN ASM_SIMP_TAC[] THEN MP_TAC(MESON[REAL_LE_DIV;REAL_ARITH `&0<= &1/\ &0<= &27`;REAL_ARITH `r- &1<= r+ &1`;REAL_LE_MUL;REAL_LE_ADD;REAL_ARITH ` a:real <= b /\ b<= c ==> a<= c`] `&0<= r pow 2 /\ &0<= r/\ &0<= r- &1 /\ &0 <= pi /\ &0 <= sqrt (&18) ==>  &0<= (&27 / r * (r - &1) + &27 / r pow 2 * (r - &1) * (r + &1))`) THEN ASM_SIMP_TAC[REAL_LE_MUL] THEN REPEAT DISCH_TAC THEN MP_TAC(MESON[REAL_LE_DIV;REAL_ARITH `&0<= &1`;REAL_LE_MUL;REAL_LE_ADD;REAL_ARITH ` a:real <= b /\ b<= c ==> a<= c`] `&0<= r /\ &0 <= pi /\ &0 <= c ==>  &0<= &1 / r * (c:real)`) THEN ASM_SIMP_TAC[] THEN DISCH_TAC
  THEN MATCH_MP_TAC(SPECL [`&1 / (r:real) * (c:real):real`;`&2 / (r * sqrt (&32)) * (r - &1) +
      &1 / (r pow 2 * sqrt (&32)) * (r - &1) * (r + &1):real`] REAL_LE_MUL) THEN ASM_SIMP_TAC[REAL_LE_DIV;REAL_LE_MUL;REAL_LE_ADD;REAL_ARITH ` a<= b /\ b<= c ==> a<= c`] THEN MATCH_MP_TAC(SPECL [`&2 / (r * sqrt (&32)) * (r - &1):real`;`&1 / (r pow 2 * sqrt (&32)) * (r - &1) * (r + &1):real`] REAL_LE_ADD) THEN ASM_MESON_TAC[REAL_LE_DIV;REAL_LE_MUL;REAL_LE_ADD;REAL_ARITH ` a:real <= b /\ b<= c ==> a<= c`]);;

(*-----------------------------------------------------------------*)
(*      Lemma 5.3 If exist fcc_compatible,negligible fun then OK   *)
(*-----------------------------------------------------------------*)


let JGXZYGW=prove(`!(S:real^3 ->bool).packing S /\ saturate S /\ (? (A:real^3 ->real).(fcc_compatible A S)/\ (negligible_fun A S)) ==> ? (c:real). (!(r:real)(p:real^3). &1<= r ==> measure ((UNIONS {ball(v:real^3, &1) | v IN S}) INTER ball(p,r))/ measure (ball(p, r))<= pi/ sqrt( &18) + c/ r)`,REPEAT GEN_TAC THEN REWRITE_TAC[negligible_fun;fcc_compatible] THEN REPEAT STRIP_TAC THEN MP_TAC(SPEC `C:real` ineq_lm5_3_step4) THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `c':real`
		    THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_SIMP_TAC[] THEN SUBGOAL_THEN `measure (UNIONS {ball (v,&1) | v IN (S:real^3 ->bool)} INTER ball (p:real^3,r:real)) /
     measure (ball (p,r))<= pi / sqrt (&18) * (&1 + &3 / r) pow 3 +
 (C:real) * (r + &1) pow 2 / (r pow 3 * sqrt (&32))` (fun th -> ASM_MESON_TAC[th;REAL_ARITH `a<=b/\ b<= c ==> a<= c`])
 THEN MP_TAC(SPECL [`S:real^3 ->bool`;`p:real^3`;`r:real`] measure_ineq_lm53_2) THEN ASM_SIMP_TAC[REAL_ARITH `&1<= r ==> &0<= r`] THEN DISCH_TAC THEN MP_TAC(SPECL [`S:real^3 ->bool`;`p:real^3`;`r:real`;`A:real^3 ->real`] ineq_lm5_3_step3) THEN ASM_SIMP_TAC[REAL_ARITH `&1<= r ==> &0<= r`;fcc_compatible] THEN ASM_SIMP_TAC[SUM_ADD;KIUMVTC;REAL_ARITH `&1<=r ==> &0<= r + &1`;] THEN FIRST_X_ASSUM(MP_TAC o SPECL [`r+ &1:real`;`p:real^3`]) THEN ASM_SIMP_TAC[REAL_ARITH `&1<=r ==> &1<= r+ &1`]
 THEN MP_TAC(SPECL [`S:real^3 ->bool`;`p:real^3`;`r:real`] sum_measure_voronoi_le_ball) THEN ASM_SIMP_TAC[REAL_ARITH `&1<= r ==> &0<= r`] THEN REPEAT DISCH_TAC THEN MP_TAC(REAL_ARITH  `sum ((S:real^3 ->bool) INTER ball (p:real^3,r + &1)) (\v:real^3. measure (voronoi v S)) <=
 measure (ball (p,r + &3))
 /\ sum (S INTER ball (p,r + &1)) (A:real^3 ->real) <= (C:real) * (r + &1) pow 2 /\ sqrt (&32) * &(CARD (S INTER ball (p,r + &1))) <=
     sum (S INTER ball (p,r + &1)) A +
     sum (S INTER ball (p,r + &1)) (\v:real^3. measure (voronoi v S))
 ==> sqrt (&32) * &(CARD (S INTER ball (p,r + &1))) <= C * (r + &1) pow 2 + measure (ball (p,r + &3))`) THEN ASM_SIMP_TAC[]
 THEN ASM_SIMP_TAC[VOLUME_BALL;REAL_ARITH `&1<= r ==> &0<= r+ &3`] THEN ASM_SIMP_TAC[REAL_FIELD `&1<= r ==> &4 / &3 * pi * (r + &3) pow 3 = ( &1 + &3/ r) pow 3 * (&4 / &3 * pi * r pow 3)`] THEN ASM_SIMP_TAC[GSYM (ISPECL [`p:real^3`;`r:real`] VOLUME_BALL);REAL_ARITH `&1<= r ==> &0<= r`] THEN ONCE_REWRITE_TAC[REAL_ARITH `sqrt (&32) * &(CARD ((S:real^3 -> bool) INTER ball (p:real^3,r + &1))) = &(CARD (S INTER ball (p,r + &1))) * sqrt (&32)`] THEN SIMP_TAC[GSYM REAL_LE_RDIV_EQ;MESON[SQRT_POS_LT;REAL_ARITH `&0< &32`] `&0< sqrt( &32)`] THEN DISCH_TAC THEN SUBGOAL_THEN `measure (UNIONS {ball (v,&1) | v IN (S:real^3->bool)} INTER ball (p:real^3,r:real))<= ((C:real) * (r + &1) pow 2 + (&1 + &3 / r) pow 3 * measure (ball (p,r))) /
 sqrt (&32) * &4 * pi / &3` MP_TAC THENL [(*1*)UNDISCH_TAC `(measure (UNIONS {ball (v,&1) | v IN (S:real^3 ->bool)} INTER ball (p:real^3,r:real)) <=
      &(CARD {ball (v,&1) | v IN S INTER ball (p,r + &1)}) * &4 * pi / &3):bool` THEN SUBGOAL_THEN `&(CARD {ball (v,&1) | v IN (S:real^3 ->bool) INTER ball (p:real^3,r + &1)}) * &4 * pi / &3 <= ((C:real) * (r + &1) pow 2 + (&1 + &3 / r) pow 3 * measure (ball (p,r))) /
     sqrt (&32) *
     &4 *
     pi / &3` (fun th -> MESON_TAC[th;REAL_ARITH `a<= b /\ b<= c ==> a<= c`]) THEN ASM_MESON_TAC[card_eq_ball_point;REAL_ARITH `&1<= r ==> &0<= r`;REAL_OF_NUM_EQ;MESON[PI_POS;REAL_ARITH `&0< &4 /\ &0< &3`;REAL_LT_MUL;REAL_LT_DIV] `&0< &4 * pi/ &3`;REAL_ARITH `a<= b /\ b<= c ==> a<= c`;REAL_LE_RMUL_EQ];(*2*)ASM_SIMP_TAC[VOLUME_BALL;REAL_ARITH `&1<= r ==> &0<= r`]
   THEN MP_TAC(MESON[REAL_ARITH `&1<= r ==> &0< r`;PI_POS;REAL_ARITH `&0< &4 /\ &0< &3`;REAL_LT_MUL;REAL_LT_DIV;REAL_POW_LT] `&1<= r ==> &0< &4/ &3 *pi * r pow 3`) THEN ASM_SIMP_TAC[] THEN SIMP_TAC[REAL_LE_LDIV_EQ] THEN SUBGOAL_THEN `((C:real) * (r + &1) pow 2 + (&1 + &3 / r) pow 3 * &4 / &3 * pi * r pow 3) /
     sqrt (&32) *
     &4 *
     pi / &3= (pi / sqrt (&18) * (&1 + &3 / r) pow 3 +
      C * (r + &1) pow 2 / (r pow 3 * sqrt (&32))) *
     &4 / &3 *
     pi *
     r pow 3` (fun th -> MESON_TAC[th]) THEN REWRITE_TAC[REAL_FIELD `((a:real) + b)/ c * d= ((a + b)*d )/c /\ ((x:real) + y ) * z = x *z + y* z`] THEN ASM_SIMP_TAC[REAL_EQ_LDIV_EQ;MESON[SQRT_POS_LT;REAL_ARITH `&0< &32`] `&0< sqrt( &32)`;REAL_FIELD `((x:real) + y ) * z = x *z + y* z`] THEN SUBGOAL_THEN `(C * (r + &1) pow 2) * &4 * pi / &3 = ((C * (r + &1) pow 2 / (r pow 3 * sqrt (&32))) * &4 / &3 * pi * r pow 3) *
 sqrt (&32) /\ ((&1 + &3 / r) pow 3 * &4 / &3 * pi * r pow 3) * &4 * pi / &3 = ((pi / sqrt (&18) * (&1 + &3 / r) pow 3) * &4 / &3 * pi * r pow 3) *
 sqrt (&32)` (fun th -> MESON_TAC[th;REAL_ARITH ` a= b /\ d= c ==> a+ d= c+ b`]) THEN STRIP_TAC
THENL [(*2a*)REWRITE_TAC[REAL_FIELD `((C * (r + &1) pow 2 / (r pow 3 * sqrt (&32))) * &4 / &3 * pi * r pow 3) *
 sqrt (&32)= ((C * (r + &1) pow 2 / (r pow 3 * sqrt (&32)))*(r pow 3 * sqrt (&32)))* (&4 / &3 * pi)`]
  THEN MATCH_MP_TAC (REAL_FIELD `~ (r pow 3 * sqrt (&32) = &0)==>(C * (r + &1) pow 2) * &4 * pi / &3=  ((C * (r + &1) pow 2 / (r pow 3 * sqrt (&32)))*(r pow 3 * sqrt (&32)))* (&4 / &3 * pi)`) THEN ASM_MESON_TAC[REAL_DIV_RMUL;REAL_MUL_ASSOC;REAL_MUL_SYM;REAL_ENTIRE;MESON[REAL_POW_NZ;REAL_ARITH `&1<= r ==> ~ (r= &0)`] `&1<=r ==> ~ (r pow 3 = &0)`;MESON[REAL_ARITH `&0< x ==> ~ (x= &0)`;SQRT_POS_LT;REAL_ARITH `&0< &32`] ` ~ (sqrt( &32) = &0)`];(*2b*)REWRITE_TAC[REAL_FIELD `((pi / sqrt (&18) * (&1 + &3 / r) pow 3) * &4 / &3 * pi * r pow 3) *
		 sqrt (&32)= ((pi* sqrt( &32) / sqrt (&18)) * (&1 + &3 / r) pow 3) * &4 / &3 * pi * r pow 3`]
  THEN SUBGOAL_THEN `sqrt (&32) / sqrt (&18)= &4/ &3`  (fun th -> REWRITE_TAC[th;REAL_FIELD `((&1 + &3 / r) pow 3 * &4 / &3 * pi * r pow 3) * &4 * pi / &3 = ((pi * &4/ &3) * (&1 + &3 / r) pow 3) * &4 / &3 * pi * r pow 3`]) THEN ONCE_REWRITE_TAC[REAL_ARITH ` &32= &4 pow 2  * &2 /\ &18= &3 pow 2 * &2`] THEN SIMP_TAC[SQRT_MUL;REAL_ARITH ` &0<= &2 /\ &0<= &3 pow 2 /\ &0<= &4 pow 2`;POW_2_SQRT;REAL_ARITH `&0<= &3 /\ &0<= &4`] THEN MATCH_MP_TAC(REAL_FIELD `~ (sqrt( &2) = &0) ==> (&4 * sqrt (&2)) / (&3 * sqrt (&2)) = &4 / &3`) THEN MESON_TAC[REAL_ARITH `&0< x ==> ~ (x= &0)`;MESON[SQRT_POS_LT;REAL_ARITH `&0< &2`] ` &0< sqrt ( &2)`]]]);;


(*-------------------------------------------------------------------*)
