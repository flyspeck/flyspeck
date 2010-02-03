(*Nguyen Tat Thang*)
 
(* edited by esusick to be compatible with new definitions on 11/12/2009 svn 1296 *)

(*
needs "Multivariate/flyspeck.ml";;
needs "Multivariate/vectors.ml";;     

needs "Examples/card.ml";;
needs "Multivariate/topology.ml";;
needs "Examples/floor.ml";;
needs "Multivariate/measure.ml";;
needs "general/sphere.hl";;

*)


let sphere= new_definition`sphere x=(?(v:real^3)(r:real). (r> &0)/\ (x={w:real^3 | norm (w-v)= r}))`;;


(* old definitions added by thales Nov 11, 2009 *)
let radial_norm = new_definition `radial_norm r x C <=> (C SUBSET normball x r) /\ (!u. (x+u) IN C ==> (!t.(t> &0) /\ (t* norm u < r)==>(x+ t % u) IN C))`;;

let eventually_radial_norm = new_definition `eventually_radial_norm x C <=> (?r. (r> &0) /\ radial_norm r x (C INTER normball x r))`;;


(* It is enough to work with one branch of the cone.  This
simplifies the definition a bit *)
(*
let c_cone = new_definition `c_cone (v,w:real^3, r:real)={x:real^3 | (x=v) \/ ((x-v) dot w 
= norm (x-v)* norm w* r)\/ ((x-v) dot w = --norm (x-v)* norm w* r)}`;;
*)
let c_cone = new_definition `c_cone (v,w:real^3, r:real)={x:real^3 | ((x-v) dot w = norm (x-v)* norm w* r)}`;;

(* let circular_cone2 =new_definition `circular_cone2 (V:real^3-> bool)=
(? (v,w:real^3)(r:real). V= c_cone (v,w,r))`;;

let NULLSET_RULES,NULLSET_INDUCT,NULLSET_CASES =
  new_inductive_definition
    `(!P. ((plane P)\/ (sphere P) \/ (circular_cone2 P)) ==> NULLSET P) /\
     !(s:real^3->bool) t. (NULLSET s /\ NULLSET t) ==> NULLSET (s UNION t)`;;*)


let null_equiv = new_definition `null_equiv (s,t :real^3->bool)=(? (B:real^3-> bool). NULLSET B  /\
((s DIFF t) UNION (t DIFF s)) SUBSET B)`;;


(*Radial*)
(* moved to definitions_kepler.ml *)
(*
let radial = new_definition `radial r x C <=> (C SUBSET ball (x,r)) /\ (!u. (x+u) IN C ==> (!t.(t> &0) /\ (t* norm u < r)==>(x+ t % u) IN C))`;;

let eventually_radial = new_definition `eventually_radial x C <=> (?r. (r> &0) /\ radial r x (C INTER ball (x,r)))`;;
*)


(*----------------------------------------------------------*)

(*To prove Lemma 4.2*)

let th1= prove(`!a b c. [a; b; c]= CONS a (CONS b [c])`,REPEAT GEN_TAC THEN MESON_TAC[]);;

let dodai=prove(`!a b c. LENGTH [a; b; c] = 3`,REPEAT GEN_TAC THEN REWRITE_TAC[LENGTH;th1] THEN ARITH_TAC);;

let th3=prove(`!i. (1<=i /\ i<= 3)==>(vec 1:real^3)$i= &1`,GEN_TAC THEN DISCH_TAC THEN (ASM_SIMP_TAC[VEC_COMPONENT;DIMINDEX_3]));;

let identity_scale=prove(`scale (vec 1)= I`,REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN REWRITE_TAC[I_THM] THEN REWRITE_TAC[scale] THEN REWRITE_TAC[vector] THEN SIMP_TAC[dodai] THEN REWRITE_TAC[CART_EQ] THEN REWRITE_TAC[DIMINDEX_3] THEN GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA;DIMINDEX_3] THEN MP_TAC (ARITH_RULE `(1 <= i /\ i <= 3) <=> ( i=1 \/ i=2 \/ i=3)`) THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL [ASM_REWRITE_TAC[];ASM_REWRITE_TAC[];ASM_REWRITE_TAC[]] THENL [ASM_REWRITE_TAC[ARITH_RULE `1-1=0`];REWRITE_TAC[ARITH_RULE `2-1= SUC 0 `];REWRITE_TAC[ARITH_RULE `3-1= SUC 1 `]] THENL [REWRITE_TAC[EL];REWRITE_TAC[EL];REWRITE_TAC[EL]] THENL [REWRITE_TAC[HD];REWRITE_TAC[HD;TL];REWRITE_TAC[ARITH_RULE `1= SUC 0 `;EL]] THENL [SIMP_TAC[th3;ARITH_RULE `1<=1 /\ 1<=3`];SIMP_TAC[th3;ARITH_RULE `1<=2 /\ 2<=3`];REWRITE_TAC[HD;TL]] THENL [ARITH_TAC;ARITH_TAC;REWRITE_TAC[ARITH_RULE `SUC 0=1`]] THEN SIMP_TAC[th3;ARITH_RULE `1<=3 /\ 3<=3`] THEN ARITH_TAC);;

let th4=prove(`!(S: A->bool). IMAGE I S= S`,GEN_TAC THEN REWRITE_TAC[IMAGE] THEN REWRITE_TAC[I_THM] THEN SET_TAC[]);;

let SET_EQ=prove(`(A: real^3 -> bool) = B <=> (!a. a IN A ==> a IN B) /\ (!a. a IN B ==> a IN A)`,SET_TAC[]);;

let scale_mul=prove(`!(s:real) t x. (scale (s%(t:real^3)) (x:real^3):real^3) = s% scale t x`,REPEAT GEN_TAC THEN REWRITE_TAC[scale] THEN REWRITE_TAC[vector] THEN SIMP_TAC[dodai] THEN REWRITE_TAC[CART_EQ] THEN REWRITE_TAC[DIMINDEX_3] THEN ASM_REWRITE_TAC[ARITH_RULE `(1 <= i /\ i <=3) <=> i =1 \/ i=2 \/ i=3`] THEN GEN_TAC THEN STRIP_TAC THENL [ASM_REWRITE_TAC[LAMBDA_BETA];ASM_REWRITE_TAC[];ASM_REWRITE_TAC[]] THENL [SIMP_TAC[LAMBDA_BETA;DIMINDEX_3;ARITH_RULE `1<=1 /\ 1<=3`];SIMP_TAC[VECTOR_MUL_COMPONENT;LAMBDA_BETA;DIMINDEX_3;ARITH_RULE `1<=2 /\ 2<=3`];SIMP_TAC[VECTOR_MUL_COMPONENT;LAMBDA_BETA;DIMINDEX_3;ARITH_RULE `1<=3 /\ 3<=3`]] THENL [SIMP_TAC[VECTOR_MUL_COMPONENT;DIMINDEX_3;ARITH_RULE `1<=1 /\ 1<=3`
];REWRITE_TAC[EL;ARITH_RULE `2-1=SUC 0`];REWRITE_TAC[EL;ARITH_RULE `3-1=SUC 1`]] THENL [SIMP_TAC[LAMBDA_BETA;DIMINDEX_3;ARITH_RULE `1<=1 /\ 1<=3`];REWRITE_TAC[HD;TL];REWRITE_TAC[EL;ARITH_RULE `1=SUC 0`]] THENL [REWRITE_TAC[ARITH_RULE `1-1=0`;EL];ARITH_TAC;REWRITE_TAC[HD;TL]] THENL[REWRITE_TAC[HD];ARITH_TAC] THEN ARITH_TAC);;

let normball_ellip0=prove(`!r. normball (vec 0:real^3) r = ellipsoid (vec 1) r`,GEN_TAC THEN REWRITE_TAC[ellipsoid] THEN REWRITE_TAC[SET_EQ] THEN STRIP_TAC THENL [GEN_TAC;GEN_TAC] THENL [REWRITE_TAC[IN_IMAGE];REWRITE_TAC[IN_IMAGE]] THENL [DISCH_TAC;SIMP_TAC[identity_scale]] THENL [(EXISTS_TAC `a:real^3`);REWRITE_TAC[I_THM]] THENL [CONJ_TAC;REPEAT STRIP_TAC] THENL [SIMP_TAC[identity_scale];ASM_REWRITE_TAC[];ASM_REWRITE_TAC[]] THEN REWRITE_TAC[I_THM]);;

let trans_normball=prove(`!(x:real^3) r. normball x r = IMAGE ((+) x) (normball (vec 0) r)`,REPEAT GEN_TAC THEN REWRITE_TAC[SET_EQ] THEN STRIP_TAC THENL [GEN_TAC;GEN_TAC] THENL [REWRITE_TAC[IN_IMAGE;normball];REWRITE_TAC[IN_IMAGE;normball]] THENL [REWRITE_TAC[IN_ELIM_THM];REWRITE_TAC[IN_ELIM_THM]] THENL [REWRITE_TAC[dist];REWRITE_TAC[dist]] THENL [DISCH_TAC;REWRITE_TAC[VECTOR_SUB_RZERO]] THENL [EXISTS_TAC `a-x:real^3`;REPEAT STRIP_TAC] THENL [REWRITE_TAC[VECTOR_ADD_SUB];ASM_REWRITE_TAC[]] THENL [CONJ_TAC;REWRITE_TAC[VECTOR_ADD_SUB]] THENL [REWRITE_TAC[VECTOR_SUB_ADD2];REWRITE_TAC[VECTOR_SUB_RZERO];ASM_REWRITE_TAC[]] THEN ASM_REWRITE_TAC[]);;

let measurable_normball0=prove(`!r. measurable (normball (vec 0:real^3) r)`,GEN_TAC THEN MESON_TAC[primitive;MEASURABLE_RULES;normball_ellip0]);;

let measurable_normball=prove(`!(x:real^3) r. measurable (normball x r)`,REPEAT GEN_TAC THEN MESON_TAC[MEASURABLE_RULES;trans_normball;measurable_normball0]);;

let rsduong=prove(`!(s:real) (r:real). (s> &0) /\ (s<r)==> r/s> &0`,REPEAT GEN_TAC THEN STRIP_TAC THEN UNDISCH_TAC `(s> &0):bool` THEN REWRITE_TAC[ARITH_RULE `s> &0 <=> &0 <s`] THEN SIMP_TAC[REAL_LT_RDIV_EQ] THEN REWRITE_TAC[ARITH_RULE `&0*s= &0`] THEN ASM_REAL_ARITH_TAC);;

let rsnon_zero=prove(`!(s:real) (r:real). (s> &0) /\ (s<r)==> ~(r/s= &0)`,REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `r/s> &0` MP_TAC THENL[ASM_SIMP_TAC[rsduong];REAL_ARITH_TAC]);;

let rduong=prove(`!(s:real) (r:real). (s> &0) /\ (s<r)==> (r> &0)`,REPEAT GEN_TAC THEN STRIP_TAC THEN UNDISCH_TAC `(s<r):bool` THEN UNDISCH_TAC `(s> &0):bool`THEN REAL_ARITH_TAC);;

let rnon_zero=prove(`!(s:real) (r:real). (s> &0) /\ (s<r)==> ~(r= &0)`,REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `r> &0` MP_TAC THENL[UNDISCH_TAC `(s<r):bool`THEN UNDISCH_TAC `(s> &0):bool`THEN REWRITE_TAC[TAUT `A==>B ==> C <=> A/\B==>C`];REAL_ARITH_TAC] THEN ASM_REWRITE_TAC[rduong]);;

let rs_sr_unit= prove(`!(s:real) (r:real). (s> &0) /\ (s<r)==> (s / r * r / s= &1)`,
REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `~(r/s= &0)` MP_TAC
THENL [UNDISCH_TAC `(s<r):bool`THEN UNDISCH_TAC `(s> &0):bool`THEN REWRITE_TAC[TAUT `A==>B ==> C <=> A/\B==>C`];STRIP_TAC]
THENL [ASM_REWRITE_TAC[rsnon_zero];SUBGOAL_THEN `r/s= inv(s/r)` MP_TAC] 
THENL [UNDISCH_TAC `~(r / s = &0):bool`;SIMP_TAC[]]
THENL [ASM_SIMP_TAC[REAL_INV_DIV];DISCH_TAC]
THEN SUBGOAL_THEN `~(s/r= &0)` MP_TAC
THENL [MP_TAC(ARITH_RULE `s> &0 ==> ~(s= &0)`);SIMP_TAC[REAL_MUL_RINV]]
THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[CONTRAPOS_THM]
THEN DISCH_TAC THEN SUBGOAL_THEN `r*s/r = r* &0` MP_TAC
THENL [REWRITE_TAC[ARITH_RULE `r * s / r = r * &0 <=> r * s / r - r * &0 = &0`];SUBGOAL_THEN `~(r= &0)` MP_TAC]
THENL [REWRITE_TAC[ARITH_RULE `r * s / r - r * &0 = r*(s/r- &0)`];UNDISCH_TAC `(s<r):bool`THEN UNDISCH_TAC `(s> &0):bool`THEN REWRITE_TAC[TAUT `A==>B ==> C <=> A/\B==>C`];ASM_SIMP_TAC[REAL_DIV_LMUL]]
THENL [ASM_REWRITE_TAC[];ASM_REWRITE_TAC[rnon_zero];REAL_ARITH_TAC]
THEN ARITH_TAC);;


let SQRT_MUL_POW_2= prove(`!(a:real) b. (a>= &0) /\ (b>= &0) ==> sqrt((a*a)*b)= a* sqrt(b)`,
REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `a*a>= &0` MP_TAC
THENL [REWRITE_TAC[ARITH_RULE `s>= &0 <=> &0<= s`];DISCH_TAC THEN UNDISCH_TAC `(b>= &0):bool`]
THENL [SIMP_TAC[REAL_LE_SQUARE];REWRITE_TAC[ARITH_RULE `s>= &0 <=> &0<= s`]]
THEN UNDISCH_TAC `(a * a >= &0):bool` THEN REWRITE_TAC[ARITH_RULE `a*a>= &0 <=> &0 <= a*a`]
THEN REWRITE_TAC[TAUT `A==>B ==>C <=> A/\ B ==> C`]
THEN SIMP_TAC[SQRT_MUL] THEN SUBGOAL_THEN `sqrt(a*a)= a` MP_TAC
THENL [UNDISCH_TAC `(a>= &0):bool`;MESON_TAC[]]
THEN REWRITE_TAC[ARITH_RULE `s>= &0 <=> &0<= s`]
THEN SIMP_TAC[SQRT_MUL] THEN SIMP_TAC[SQRT_POW_2] THEN MESON_TAC[REAL_POW_2;SQRT_POW_2]);;

g `!r s (x:real^3) C. radial_norm r x C /\ (s > &0) /\ (s < r) ==> (C INTER normball x s = IMAGE ((+) x) (IMAGE (scale (s/r % (vec 1)))(IMAGE ((+) (--x)) (C INTER normball x r))))`;;

e (REPEAT GEN_TAC THEN STRIP_TAC);;

e (REWRITE_TAC[SET_EQ] THEN CONJ_TAC THEN GEN_TAC);;

e (REWRITE_TAC[IN_INTER;IN_IMAGE]);;

e (STRIP_TAC);;

e (EXISTS_TAC `a-x:real^3`);;

e (REWRITE_TAC[VECTOR_ARITH `(a:real^3)= x+a-x`]);;

e (EXISTS_TAC `scale (r/s% vec 1)(a-x):real^3`);;

e (SIMP_TAC[scale_mul] THEN SIMP_TAC[identity_scale] THEN REWRITE_TAC[I_THM]);;

e (REWRITE_TAC[VECTOR_MUL_ASSOC]);;

e (UNDISCH_TAC `(s> &0):bool` THEN UNDISCH_TAC `(s<r):bool` THEN REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (SIMP_TAC[rs_sr_unit]);;

e (STRIP_TAC);;

e (CONJ_TAC);;

e (VECTOR_ARITH_TAC);;

e (EXISTS_TAC `(x+r / s % (a - x)):real^3`);;

e (CONJ_TAC);;

e (VECTOR_ARITH_TAC);;

e (CONJ_TAC);;

e (SUBGOAL_THEN `(x:real^3)+(a-x) IN (C:real^3->bool)` MP_TAC);;

e (UNDISCH_TAC `(a:real^3 IN (C:real^3->bool)):bool`);;

e (MP_TAC(VECTOR_ARITH `(a:real^3)=x+(a-x)`));;

e (REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (SET_TAC[]);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `(r/s)> &0 /\ (r/s) * (norm (a:real^3-x):real)< r` MP_TAC);;

e (UNDISCH_TAC `(s> &0):bool` THEN UNDISCH_TAC `(s<r):bool` THEN REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (SIMP_TAC[rsduong]);;

e (STRIP_TAC);;

e (UNDISCH_TAC `(a:real^3 IN normball x s):bool`);;

e (REWRITE_TAC[normball]);;

e (REWRITE_TAC[IN_ELIM_THM;dist]);;

e (ABBREV_TAC `c= norm(a:real^3 -x)`);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `r/s> &0` MP_TAC);;

e (UNDISCH_TAC `(s<r):bool` THEN UNDISCH_TAC `(s> &0):bool` THEN REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (SIMP_TAC[rsduong]);;

e (REWRITE_TAC[ARITH_RULE `s> &0 <=> &0< s`]);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `r/s*c < r/s*s` MP_TAC);;

e (UNDISCH_TAC `(c < s):bool` THEN UNDISCH_TAC `(&0< r/s):bool` THEN REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (REWRITE_TAC[TAUT `A/\B==>C <=> B/\A==>C`] THEN REWRITE_TAC[ARITH_RULE `r / s * c < r / s * s <=> c*r/s < s*r/s`]);;

e (REWRITE_TAC[REAL_LT_RMUL]);;

e (MP_TAC(ARITH_RULE `s> &0 ==> ~(s= &0)`));;

e (ASM_REWRITE_TAC[]);;

e (REWRITE_TAC[TAUT `A==>B==>C <=>A/\B==>C`]);;

e (SIMP_TAC[]);;

e (MESON_TAC[REAL_DIV_RMUL]);;

e (ASM_MESON_TAC[radial_norm]);;

e (REWRITE_TAC[normball;IN_ELIM_THM;dist]);;

e (REWRITE_TAC[VECTOR_ARITH `((x:real^3) + r / s % (a - x)) - x= r / s % (a - x)`]);;

e (REWRITE_TAC[vector_norm]);;

e (REWRITE_TAC[VECTOR_ARITH `r / s % ((a:real^3) - x) dot r / s % (a - x)= (r/s *r/s) * (a-x) dot (a-x)`]);;

e (SUBGOAL_THEN `r/s> &0` MP_TAC);;

e (UNDISCH_TAC `(s<r):bool` THEN UNDISCH_TAC `(s> &0):bool` THEN REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (REWRITE_TAC[rsduong]);;

e (DISCH_TAC);;

e (UNDISCH_TAC `(a IN normball (x:real^3) s):bool`);;

e (REWRITE_TAC[normball;IN_ELIM_THM;dist]);;

e (REWRITE_TAC[vector_norm]);;

e (ABBREV_TAC `q2= (a:real^3 - x) dot (a - x)`);;

e (DISCH_TAC);;

e (UNDISCH_TAC `(sqrt q2 < s):bool`);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `q2>= &0` MP_TAC);;


e (REWRITE_TAC[ARITH_RULE `q2>= &0 <=> &0<= q2`]);;

e (ASM_MESON_TAC[DOT_POS_LE]);;

e (MP_TAC(ARITH_RULE `r/s> &0 ==> r/s>= &0`));;

e (ASM_REWRITE_TAC[]);;

e (REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (SIMP_TAC[SQRT_MUL_POW_2]);;

e (STRIP_TAC);;

e (SUBGOAL_THEN `r/s*sqrt q2<r/s * s` MP_TAC);;

e (REWRITE_TAC[ARITH_RULE `r / s * sqrt q2 < r / s * s<=> sqrt q2* r/s< s* r/s`]);;

e (UNDISCH_TAC `(r / s > &0):bool` THEN REWRITE_TAC[ARITH_RULE `r / s > &0<=> &0< r/s`] THEN UNDISCH_TAC `(sqrt q2 < s):bool`);;

e (REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (SIMP_TAC[REAL_LT_RMUL]);;

e (MP_TAC(ARITH_RULE `s> &0==> ~(s= &0)`));;

e (ASM_REWRITE_TAC[]);;

e (MESON_TAC[REAL_DIV_RMUL]);;

e (REWRITE_TAC[IN_IMAGE;IN_INTER]);;

e (REWRITE_TAC[scale_mul;identity_scale;I_THM]);;

e(STRIP_TAC THEN CONJ_TAC);;

e (ASM_SIMP_TAC[]);;

e (SUBGOAL_THEN `(x:real^3) + (--x + x''') IN C` MP_TAC);;

e (MP_TAC(VECTOR_ARITH `x'''= (x:real^3)+ (--x + x''')`));;

e (ABBREV_TAC `u1= (x:real^3) + --x + x'''`);;

e (UNDISCH_TAC `(x''' IN (C:real^3->bool)):bool`);;

e (REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (SET_TAC[]);;

e (SUBGOAL_THEN `s/r> &0 /\s/r* norm (--x+ x''':real^3)< r` MP_TAC);;


e (CONJ_TAC);;

e (MP_TAC(ARITH_RULE `s<r /\ s> &0 ==> r> &0`));;

e (ASM_REWRITE_TAC[]);;

e (REWRITE_TAC[ARITH_RULE `a> &0 <=> &0<a`]);;

e (REWRITE_TAC[REAL_LT_LDIV_EQ]);;

e (REWRITE_TAC[REAL_LT_RDIV_EQ]);;

e (SIMP_TAC[REAL_LT_RDIV_EQ]);;

e (REWRITE_TAC[ARITH_RULE `&0*r= &0`]);;

e (DISCH_TAC);;

e (ASM_REWRITE_TAC[]);;

e (REWRITE_TAC[ARITH_RULE `&0< s <=> s> &0`]);;

e (ASM_REWRITE_TAC[]);;

e (SUBGOAL_THEN `s/r> &0` ASSUME_TAC);;

e (MP_TAC(ARITH_RULE `s<r /\ s> &0 ==> r> &0`) THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `a> &0 <=> &0<a`] THEN REWRITE_TAC[REAL_LT_LDIV_EQ] THEN REWRITE_TAC[REAL_LT_RDIV_EQ] THEN SIMP_TAC[REAL_LT_RDIV_EQ] THEN REWRITE_TAC[ARITH_RULE `&0*r= &0`] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `&0< s <=> s> &0`] THEN ASM_REWRITE_TAC[]);;

e (SUBGOAL_THEN `s/r< &1` ASSUME_TAC);;

e (MP_TAC(ARITH_RULE `s<r /\ s> &0 ==> r> &0`));;

e (ASM_REWRITE_TAC[]);;

e (REWRITE_TAC[ARITH_RULE `r> &0 <=> &0 <r`]);;

e (REWRITE_TAC[ARITH_RULE `&1 * r= r`]);;

e (DISCH_TAC);;

e (ASM_REWRITE_TAC[]);;

e (UNDISCH_TAC `( &0<r):bool`);;

e (SIMP_TAC[REAL_LT_LDIV_EQ]);;


e (REWRITE_TAC[ARITH_RULE `&1*r=r`]);;

e (DISCH_TAC);;

e (ASM_REWRITE_TAC[]);;

e (UNDISCH_TAC `(x''':real^3 IN normball x r):bool`);;

e (REWRITE_TAC[normball;IN_ELIM_THM;dist]);;

e (SUBGOAL_THEN `norm (x''':real^3 - x)= norm (--x + x''')` ASSUME_TAC);;

e (MP_TAC(VECTOR_ARITH `x''':real^3 - x = --x + x'''`));;

e (ABBREV_TAC `v1= x''':real^3 - x`);;

e (MESON_TAC[]);;

e (ASM_SIMP_TAC[]);;

e (SUBGOAL_THEN `&0<= norm (--x + x''':real^3)` MP_TAC);;

e (SIMP_TAC[NORM_POS_LE]);;

e (REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (MP_TAC(ARITH_RULE `s/r> &0 /\ s/r< &1==> &0<= s/r /\ s/r< &1`));;

e (ASM_REWRITE_TAC[]);;

e (REWRITE_TAC[TAUT `A==>B/\C==>D <=> A/\B/\C==>D`]);;

e (ABBREV_TAC `y= norm (--x + x''':real^3)`);;

e (UNDISCH_TAC `(s / r < &1):bool`);;

e (REWRITE_TAC[TAUT `A==>B/\C/\D==>E <=> (B/\A/\C/\D==>E)`]);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `s/r*y< &1*r` MP_TAC);;

e (UNDISCH_TAC `(&0 <= s / r /\ s / r < &1 /\ &0 <= y /\ y < r):bool`);;

e (MESON_TAC[REAL_LT_MUL2]);;

e (MESON_TAC[ARITH_RULE `&1*r= r`]);;

e (REWRITE_TAC[TAUT `A/\B==>C==>D <=> A/\B/\C==>D`]);;

e (ASM_MESON_TAC[radial_norm]);;

e (ASM_REWRITE_TAC[]);;

e (REWRITE_TAC[normball;IN_ELIM_THM;dist]);;

e (REWRITE_TAC[VECTOR_ARITH `(x + s / r % (--x + x''')) - x= s / r % (--x + x''')`]);;

e (SIMP_TAC[NORM_MUL]);;

e (SUBGOAL_THEN `s/r> &0` ASSUME_TAC);;

e (MP_TAC(ARITH_RULE `s<r /\ s> &0 ==> r> &0`) THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `a> &0 <=> &0<a`] THEN REWRITE_TAC[REAL_LT_LDIV_EQ] THEN REWRITE_TAC[REAL_LT_RDIV_EQ] THEN SIMP_TAC[REAL_LT_RDIV_EQ] THEN REWRITE_TAC[ARITH_RULE `&0*r= &0`] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH_RULE `&0< s <=> s> &0`] THEN ASM_REWRITE_TAC[]);;

e (MP_TAC(ARITH_RULE `s/r> &0==> s/r>= &0`));;

e (ASM_REWRITE_TAC[]);;

e (REWRITE_TAC[ARITH_RULE `s/r>= &0 <=> &0<= s/r`]);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `abs (s / r)= s/r` MP_TAC);;

e (ASM_SIMP_TAC[REAL_ABS_REFL]);;

e (SIMP_TAC[]);;

e (DISCH_TAC);;

e (UNDISCH_TAC `(x''':real^3 IN normball x r):bool`);;

e (REWRITE_TAC[normball;IN_ELIM_THM;dist]);;

e (SUBGOAL_THEN `norm (x''':real^3 - x)= norm (--x + x''')` ASSUME_TAC);;

e (MP_TAC(VECTOR_ARITH `x''':real^3 - x = --x + x'''`));;


e (ABBREV_TAC `v2= x''':real^3 - x`);;

e (MESON_TAC[]);;

e (ASM_SIMP_TAC[]);;

e (ABBREV_TAC `p= norm (--x + x''':real^3)`);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `p*s/r< r*s/r` MP_TAC);;

e (MP_TAC(ARITH_RULE `s / r > &0 ==> &0< s/r`));;

e (ASM_REWRITE_TAC[]);;

e (UNDISCH_TAC `(p < r):bool` THEN REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (SIMP_TAC[REAL_LT_RMUL]);;

e (REWRITE_TAC[ARITH_RULE `s/r*p<s <=> p*s/r< s`]);;

e (MP_TAC(ARITH_RULE `s<r/\s> &0 ==> ~(r= &0)`));;

e (ASM_REWRITE_TAC[]);;

e (REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (MESON_TAC[REAL_DIV_LMUL]);;


let trans_strech_trans_radial=top_thm();;


(*----------------------------------------------*)

(* Lemma 4.2*)

(* changed volume_props to volume_prop in the rest of this file. volume_props uses ball in the definition and volume_prop 
   uses normball in the definition*)

let volume_prop = new_definition `volume_prop  (vol:(real^3->bool)->real) = 
    ( (!C. vol C >= &0) /\
     (!Z. NULLSET Z ==> (vol Z = &0)) /\
     (!X Y. measurable X /\ measurable Y /\ NULLSET (SDIFF X Y) ==> (vol X = vol Y)) /\
     (!X t. (measurable X) /\ (measurable (IMAGE (scale t) X)) ==> (vol (IMAGE (scale t) X) = abs(t$1 * t$2 * t$3)*vol(X))) /\
     (!X v. measurable X ==> (vol (IMAGE ((+) v) X) = vol X)) /\
     (!v0 v1 v2 v3 r. (r > &0) /\ (~(collinear {v0,v1,v2})) /\ ~(collinear {v0,v1,v3}) ==> vol (solid_triangle v0 {v1,v2,v3} r) = vol_solid_triangle v0 v1 v2 v3 r) /\
     (!v0 v1 v2 v3. vol(conv0 {v0,v1,v2,v3}) = vol_conv v0 v1 v2 v3) /\
     (!v0 v1 v2 v3 h a. ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) /\ (h >= &0) /\ (a > &0) /\ (a <= &1) ==> vol(frustt v0 v1 h a INTER wedge v0 v1 v2 v3) = vol_frustt_wedge v0 v1 v2 v3 h a) /\
     (!v0 v1 v2 v3 r c.  ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) /\ (r >= &0) /\ (c >= -- (&1)) /\ (c <= &1) ==> (vol(conic_cap v0 v1 r c INTER wedge v0 v1 v2 v3) = vol_conic_cap_wedge v0 v1 v2 v3 r c)) /\ 
     (!(a:real^3) (b:real^3). vol(rect a b) = vol_rect a b) /\
     (!v0 v1 v2 v3 r. ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) /\ (r >= &0)  ==> (vol(normball v0 r INTER wedge v0 v1 v2 v3) = vol_ball_wedge v0 v1 v2 v3 r)))`;;


g `! (C:real^3->bool) (x:real^3) r s. measurable C /\ volume_prop (vol) /\ radial_norm r x C /\ (s > &0) /\ (s < r) ==> measurable (C INTER normball x s) /\ vol (C INTER normball x s)= vol (C) *(s/r) pow 3`;;

e (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC);;

e (ASM_MESON_TAC[MEASURABLE_RULES;measurable_normball]);;

e (SUBGOAL_THEN `C INTER normball x s = IMAGE ((+) x) (IMAGE (scale (s/r % (vec 1)))(IMAGE ((+) (--x)) (C INTER normball x r)))` ASSUME_TAC);;

e (ASM_SIMP_TAC[trans_strech_trans_radial]);;

e (ASM_REWRITE_TAC[]);;

e (SUBGOAL_THEN `measurable ((C:real^3->bool) INTER normball x r)` ASSUME_TAC);;

e (ASM_MESON_TAC[MEASURABLE_RULES;measurable_normball]);;

e (SUBGOAL_THEN `measurable (IMAGE ((+) (--x)) ((C:real^3->bool) INTER normball x r))` ASSUME_TAC);;

e (ASM_MESON_TAC[MEASURABLE_RULES]);;

e (SUBGOAL_THEN `measurable (IMAGE (scale (s / r % vec 1)) (IMAGE ((+) (--x)) (C INTER normball x r)))` ASSUME_TAC);;

e (ASM_MESON_TAC[MEASURABLE_RULES]);;

e (SUBGOAL_THEN `measurable (IMAGE ((+) x)
 (IMAGE (scale (s / r % vec 1)) (IMAGE ((+) (--x)) (C INTER normball x r))))` ASSUME_TAC);;

e (ASM_MESON_TAC[MEASURABLE_RULES]);;

e (ABBREV_TAC `A2:real^3->bool= (IMAGE (scale (s / r % vec 1))
      (IMAGE ((+) (--x)) (C INTER normball x r)))`);;

e (SUBGOAL_THEN `vol (IMAGE ((+) x) A2)=vol (A2)` MP_TAC);;

e (UNDISCH_TAC `(volume_prop vol):bool`);;

e (UNDISCH_TAC `(measurable (A2:real^3->bool)):bool`);;

e (REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (SIMP_TAC[volume_prop]);;

e (SIMP_TAC[]);;

e (DISCH_TAC);;

e (UNDISCH_TAC `(IMAGE (scale (s / r % vec 1))
      (IMAGE ((+) (--x)) (C INTER normball x r)):real^3->bool =
      A2):bool`);;

e (REWRITE_TAC[SET_RULE `IMAGE (scale (s / r % vec 1)) (IMAGE ((+) (--x)) (C INTER normball x r)) =
 A2:real^3->bool <=> A2= IMAGE (scale (s / r % vec 1)) (IMAGE ((+) (--x)) (C INTER normball x r))`]);;

e (SIMP_TAC[]);;

e (DISCH_TAC);;


e (ABBREV_TAC `M1:real^3->bool= (IMAGE ((+) (--x)) (C INTER normball x r))`);;

e (ABBREV_TAC `w:real^3= s / r % vec 1`);;

e (SUBGOAL_THEN `vol (IMAGE (scale (w:real^3)) M1)= abs (w$1*w$2*w$3)*vol (M1)` MP_TAC);;

e (SUBGOAL_THEN `measurable (IMAGE (scale w) M1)` MP_TAC);;

e (UNDISCH_TAC `(A2 = IMAGE (scale w) M1:real^3->bool):bool`);;

e (REWRITE_TAC[SET_RULE `A2 = IMAGE (scale w) M1 <=> IMAGE (scale w) M1= A2`]);;

e (SIMP_TAC[]);;

e (ASM_MESON_TAC[]);;

e (UNDISCH_TAC `(volume_prop vol):bool`);;

e (UNDISCH_TAC `(measurable (M1:real^3->bool)):bool`);;

e (REWRITE_TAC[TAUT `P1 ==> P2 ==> P3 ==> P4 <=> P1 /\ P2 /\ P3 ==> P4`]);;

e (SIMP_TAC[volume_prop]);;

e (SIMP_TAC[]);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `((w:real^3)$1 = s/r)/\ (w$2 = s/r) /\ (w$3 = s/r)` MP_TAC);;

e (REPEAT STRIP_TAC);;

e (UNDISCH_TAC `(s / r % vec 1 = w:real^3):bool`);;

e (REWRITE_TAC[VECTOR_ARITH `s / r % vec 1 = w:real^3 <=> w= s / r % vec 1`]);;

e (SIMP_TAC[]);;

e (DISCH_TAC);;

e (SIMP_TAC[VECTOR_MUL_COMPONENT;DIMINDEX_3;ARITH_RULE `1<=1 /\ 1<=3`]);;

e (SIMP_TAC[VEC_COMPONENT;DIMINDEX_3;ARITH_RULE `1<=1 /\ 1<= 3`]);;

e (ARITH_TAC);;

e (UNDISCH_TAC `(s / r % vec 1 = w:real^3):bool`);;

e (REWRITE_TAC[VECTOR_ARITH `s / r % vec 1 = w:real^3 <=> w= s / r % vec 1`]);;

e (SIMP_TAC[]);;

e (DISCH_TAC);;

e (SIMP_TAC[VECTOR_MUL_COMPONENT;DIMINDEX_3;ARITH_RULE `1<=2 /\ 2<=3`]);;

e (SIMP_TAC[VEC_COMPONENT;DIMINDEX_3;ARITH_RULE `1<=2 /\ 2<= 3`]);;

e (ARITH_TAC);;

e (UNDISCH_TAC `(s / r % vec 1 = w:real^3):bool`);;

e (REWRITE_TAC[VECTOR_ARITH `s / r % vec 1 = w:real^3 <=> w= s / r % vec 1`]);;

e (SIMP_TAC[]);;

e (DISCH_TAC);;

e (SIMP_TAC[VECTOR_MUL_COMPONENT;DIMINDEX_3;ARITH_RULE `1<=3 /\ 3<=3`]);;

e (SIMP_TAC[VEC_COMPONENT;DIMINDEX_3;ARITH_RULE `1<=3 /\ 3<= 3`]);;

e (ARITH_TAC);;

e (SIMP_TAC[]);;

e (REWRITE_TAC[ARITH_RULE `s / r * s / r * s / r= (s/r) pow 3`]);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `s/r > &0` MP_TAC);;

e (SUBGOAL_THEN `r> &0` MP_TAC);;

e (UNDISCH_TAC `(s < r):bool` THEN UNDISCH_TAC `(s > &0):bool`);;

e (REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (MESON_TAC[rduong]);;

e (REWRITE_TAC[ARITH_RULE `(r> &0 <=> &0< r) /\ (s / r > &0 <=> &0 < s/r)`]);;

e (SIMP_TAC[REAL_LT_RDIV_EQ]);;

e (DISCH_TAC);;

e (REWRITE_TAC[ARITH_RULE `&0*r= &0`]);;

e (ASM_REWRITE_TAC[ARITH_RULE `&0< s<=> s> &0`]);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `&0<= s/r` MP_TAC);;

e (REWRITE_TAC[ARITH_RULE `&0 <= s / r <=> s/r >= &0`]);;

e (UNDISCH_TAC `(s / r > &0):bool`);;

e (ARITH_TAC);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `&0<= (s / r) pow 3` MP_TAC);;

e (UNDISCH_TAC `(&0<=s / r):bool`);;

e (MP_TAC(ARITH_RULE `&0 <= &0`));;

e (REWRITE_TAC[TAUT `a==>b==>c <=> a/\b==>c`]);;

e (DISCH_TAC);;

e (REWRITE_TAC[ARITH_RULE `&0<= (s/r) pow 3 <=> &0 pow 3<= (s/r) pow 3`]);;

e (UNDISCH_TAC `(&0 <= &0 /\ &0 <= s / r):bool`);;

e (MP_TAC(ARITH_RULE `~(3= 0)`));;

e (REWRITE_TAC[TAUT `a==>b==>c <=> a/\b==>c`]);;

e (SIMP_TAC[REAL_POW_LE2]);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `abs ((s / r) pow 3)=(s / r) pow 3` MP_TAC);;

e (SIMP_TAC[REAL_ABS_REFL]);;

e (ASM_MESON_TAC[]);;

e (SIMP_TAC[]);;

e (DISCH_TAC);;

e (REWRITE_TAC[ARITH_RULE `(s / r) pow 3 * vol M1= vol M1 * (s / r) pow 3`]);;

e (SUBGOAL_THEN `vol M1= vol C` MP_TAC);;

e (UNDISCH_TAC `(IMAGE ((+) (--x:real^3)) ((C:real^3->bool) INTER normball x r) = (M1:real^3->bool)):bool`);;

e (REWRITE_TAC[SET_RULE `IMAGE ((+) (--x)) ((C:real^3->bool) INTER normball x r) = M1 <=> M1= IMAGE ((+) (--x)) ((C:real^3->bool) INTER normball x r)`]);;

e (SIMP_TAC[]);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `vol (IMAGE ((+) (--x)) (C INTER normball x r))= vol (C INTER normball (x:real^3) r)` MP_TAC);;

e (UNDISCH_TAC `(volume_prop vol):bool`);;

e (UNDISCH_TAC `(measurable ((C:real^3->bool) INTER normball x r)):bool`);;

e (REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (SIMP_TAC[volume_prop]);;

e (SIMP_TAC[]);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `C INTER normball (x:real^3) r= C` MP_TAC);;

e (UNDISCH_TAC `(radial_norm r (x:real^3) C):bool`);;

e (REWRITE_TAC[radial_norm]);;

e (REPEAT STRIP_TAC);;

e (UNDISCH_TAC `((C:real^3->bool) SUBSET normball (x:real^3) r):bool`);;

e (SIMP_TAC[SUBSET_INTER_ABSORPTION]);;

e (DISCH_TAC);;

e (ABBREV_TAC `(E:real^3->bool)= C INTER normball x r`);;

e (ASM_MESON_TAC[]);;

e (ABBREV_TAC `a:real= (s / r) pow 3`);;

e (ABBREV_TAC `a1:real= vol M1` THEN ABBREV_TAC `a2:real= vol C`);;

e (SIMP_TAC[]);;

let lemma_r_r'=top_thm();; 

(*------------------------   Definition of Solid angle  ---------------------------------------------------------*)


let normball_subset= prove(`!(x:real^3) r r'. (r'> &0) /\ (r'<r)==> normball x r' SUBSET normball x r`, (REPEAT GEN_TAC THEN REPEAT STRIP_TAC) THEN REWRITE_TAC[SUBSET] THEN GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[normball] THEN REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[dist] THEN UNDISCH_TAC `(r' < r):bool` THEN REWRITE_TAC[TAUT `a==>b ==> c <=> a /\ b ==> c`] THEN ARITH_TAC);;
let subset_inter=prove(`! (A:real^3->bool) (B:real^3->bool). A SUBSET B ==> A INTER B= A`,REPEAT GEN_TAC THEN SET_TAC[]);;
let normball_eq=prove(`!(C:real^3->bool) x r r'. (r'> &0)/\ (r'< r)==> (C INTER normball x r) INTER normball x r' = C INTER normball x r'`,REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN (MP_TAC(SET_RULE `((C:real^3->bool) INTER normball x r) INTER normball x r'=(C INTER normball x r') INTER normball x r`)) THEN SIMP_TAC[] THEN DISCH_TAC THEN (SUBGOAL_THEN `(((C:real^3->bool) INTER normball x r') SUBSET normball x r)` MP_TAC) THENL[ASM_MESON_TAC[INTER_SUBSET;SUBSET_TRANS;normball_subset];MESON_TAC[subset_inter]]);;


let pre_def1_4_3=prove(`!(C:real^3->bool)(x:real^3). volume_prop (vol) /\ measurable C /\ eventually_radial_norm x C ==> (?s. ?c. (c > &0) /\ (!r. (r > &0) /\ (r < c) ==> (s= &3 * vol(C INTER normball x r)/(r pow 3)))) `,
 (REPEAT GEN_TAC) 
 THEN (REWRITE_TAC[eventually_radial_norm]) 
 THEN (REPEAT STRIP_TAC) 
 THEN (EXISTS_TAC `(&3* vol (C INTER normball x r) / r pow 3):real`)  
 THEN (EXISTS_TAC `(r:real)`)
 THEN (ASM_REWRITE_TAC[])
 THEN (GEN_TAC)
 THEN (REPEAT STRIP_TAC)
 THEN (REWRITE_TAC[REAL_ARITH `&3 * vol (C INTER normball x r) / r pow 3 = &3 * vol (C INTER normball x r') / r' pow 3 <=> vol (C INTER normball x r) / r pow 3 = vol (C INTER normball x r') / r' pow 3`])
 THEN (SUBGOAL_THEN `(C:real^3->bool) INTER normball x r'= (C INTER normball x r) INTER normball x r'` MP_TAC)
 THENL[ASM_MESON_TAC[normball_eq];SIMP_TAC[]] 
 THEN DISCH_TAC
 THEN (SUBGOAL_THEN `measurable ((C:real^3->bool) INTER normball x r)` ASSUME_TAC)
 THENL[ASM_MESON_TAC[MEASURABLE_RULES;measurable_normball];(SUBGOAL_THEN `vol ((C INTER normball x r) INTER normball x r')= vol (C INTER normball x r) * (r'/r) pow 3` MP_TAC)]
 THENL[ASM_MESON_TAC[lemma_r_r'];ABBREV_TAC `(a:real)=vol (C INTER normball x r)`]
 THEN ABBREV_TAC `(b:real)=vol ((C INTER normball x r) INTER normball x r')`
 THEN SIMP_TAC[] 
 THEN DISCH_TAC 
 THEN SIMP_TAC[REAL_POW_DIV] 
 THEN MP_TAC(REAL_ARITH `r'> &0 ==> ~(r'= &0)`)
 THEN ASM_REWRITE_TAC[] 
 THEN DISCH_TAC 
 THEN MP_TAC(MESON[REAL_POW_NZ] `~(r'= &0)==> ~(r' pow 3= &0)`)
 THEN ASM_REWRITE_TAC[] 
 THEN DISCH_TAC 
 THEN REWRITE_TAC[REAL_ARITH `(a * r' pow 3 / r pow 3) / r' pow 3= (a * r' pow 3/ r' pow 3)/ r pow 3`]
 THEN MP_TAC(MESON[REAL_DIV_REFL] `~(r' pow 3 = &0)==> r' pow 3 / r' pow 3= &1`) 
 THEN ASM_REWRITE_TAC[] 
 THEN SIMP_TAC[] 
 THEN DISCH_TAC 
 THEN ARITH_TAC);;  

let pre_def_4_3=prove(`?(s:(real^3->bool)->real^3 -> real). !C x. volume_prop vol /\ measurable C /\ eventually_radial_norm x C ==> (?r'.r' > &0 /\(!r. r > &0 /\ r < r' ==> s C x = &3 * vol (C INTER normball x r) / r pow 3))`,MESON_TAC[SKOLEM_THM;pre_def1_4_3]);;

let sol= new_specification ["sol"] pre_def_4_3;;



(*---------------------------------------------------------------------------------------------------------------*)



(*Lemma 4.3*)


let tr5=prove(`!r v0 C C'.(radial_norm r v0 C /\ radial_norm r v0 C' ==> (!u. ((v0+u) IN (C INTER C')) ==> (!t.(t > &0) /\ (t * norm u < r)==> (v0+t % u IN (C INTER C')))))`, REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTER] THEN MESON_TAC[radial_norm;IN_INTER]);;
let tr6=prove(`!r v0 C C'.(radial_norm r v0 C /\ radial_norm r v0 C' ==> C INTER C' SUBSET normball v0 r)`, REPEAT GEN_TAC THEN MESON_TAC[radial_norm;INTER_SUBSET;SUBSET_TRANS]);;

let inter_radial =prove(`!r v0 C C'.(radial_norm r v0 C /\ radial_norm r v0 C') ==> radial_norm r v0 (C INTER C')`, REPEAT GEN_TAC THEN MESON_TAC[radial_norm;tr5;tr6]);; 


(*4.2.11 combining solid angle and volume*)

(* removed by thales, nov 11, 2008.  Conflicts with definition of phi already provided *)

(*
let phi=new_definition `phi(h:real,t:real,l:real^2)= l$1*t*h*(t+h)/ &6 + l$2`;;
let A=new_definition `A(h:real,t:real,l:real^2)=(&1-h/t)*(phi (h,t,l)-phi (t,t,l))`;;

*)


(*-------------------------------------------------------------------------------------*)
(*                                        Finiteness                                   *)
(*-------------------------------------------------------------------------------------*)


(*------------------------------------------------------*)
(*            Useful definitions                        *)
(*------------------------------------------------------*)

let cube= new_definition `cube (x:real^3)= {y:real^3 | !i. (1<= i)/\ (i<= 3) ==> ( x$i < y$i ) /\ ( y$i < x$i + &1)}`;; 

let hinhcau=new_definition `hinhcau (x:real^3) (r:real)={y: real^3 | norm ( x - y ) < r } `;;
let set_of_cube= new_definition`set_of_cube S= {cube x| x IN S}`;;

let union_of_cube= new_definition `union_of_cube (x:real^3) (r:real)= UNIONS (set_of_cube (hinhcau x r))`;;

let int_ball= new_definition `int_ball (x:real^3) r= { y :real^3 | !i. (1<= i) /\ (i<= 3) ==> is_int (y$i)} INTER (hinhcau x r)`;;
let union_of_int_cube=new_definition `union_of_int_cube (x:real^3) (r:real) = UNIONS (set_of_cube (int_ball x r))`;;

let map0=new_definition `map0 = \(c:real^3). cube c`;;


(*-------------------------------------------------------*)
(*                 Somes lemmas                          *)
(*-------------------------------------------------------*)

let COMPONENT_LE_NORM_3=prove(`!(x:real^3) i. (1<= i) /\ (i<= 3) ==> abs (x$i)<= norm x`,MESON_TAC[COMPONENT_LE_NORM;DIMINDEX_3]);;


let component_hinhcau_bound=prove(`! (p:real^3) (r:real) x. x IN hinhcau p r ==> (!i. (1 <= i) /\ ( i <= 3 ) ==> ( p$i - r <= x$i ) /\ ( x$i <= p$i + r))`,REPEAT GEN_TAC THEN REWRITE_TAC[hinhcau] THEN REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[REAL_ARITH `(p$i):real - r <= x$i <=> p$i - x$i <= r`; REAL_ARITH `a:real <= b+c <=> -- c <= b-a`] THEN REWRITE_TAC[MESON[] `C/\B <=> B/\ C`] THEN REWRITE_TAC[GSYM REAL_ABS_BOUNDS] THEN  REWRITE_TAC[MESON[] `C/\B <=> B/\ C`] THEN REPEAT STRIP_TAC THEN MP_TAC(SPECL [`p - x:real^3`; `i:num`] COMPONENT_LE_NORM_3) THEN ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(norm (p:real^3 - x) < r):bool` THEN REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC);;

let int_interval= new_definition `int_interval (a:real) b = {x:real | is_int x /\  (a<= x) /\ (x <= b)}`;;

let finite_int_interval=prove(`! a:real b. FINITE (int_interval a b)`,REPEAT GEN_TAC THEN ASSUME_TAC (GSYM INTEGER_IS_INT) THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[INTEGER_IS_INT;FINITE_INTSEG] THEN  REWRITE_TAC[int_interval] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[FINITE_INTSEG]);;


let vector_to_pair =new_definition`vector_to_pair (x:real^3) = x$1, x$2, x$3 `;;

let lm1=prove(`!(x:real^3) (r:real) y. y IN int_ball x r ==> (!i. 1<=i /\i<= 3 ==> y$i IN int_interval (x$i - r) (x$i + r) )`,REPEAT GEN_TAC
		THEN REWRITE_TAC[int_ball;IN_ELIM_THM] THEN REWRITE_TAC[IN_INTER;IN_ELIM_THM] THEN REWRITE_TAC[int_interval;IN_ELIM_THM] THEN MESON_TAC[component_hinhcau_bound]);;


let lm2 =prove(`! (x:real^3) (r:real) y.   y IN (int_ball x r) ==> vector_to_pair y IN (int_interval (x$1 - r)  (x$1 + r) CROSS (int_interval (x$2 - r)  (x$2 + r)) CROSS (int_interval (x$3 - r)  (x$3 + r)))`,REPEAT GEN_TAC THEN REWRITE_TAC[IN_CROSS;vector_to_pair] THEN MESON_TAC[ARITH_RULE `1<=i /\ i<=3 <=> i=1\/ i=2 \/ i=3`;lm1]);;

let vector_eq1=prove(`! (x:real^3) y. x= y <=> x - y= vec 0`,REPEAT GEN_TAC THEN VECTOR_ARITH_TAC);;

let trip_eq=prove(`! (x:real^3) (y:real^3). x$1, x$2, x$3= y$1,y$2,y$3 <=> !i. 1<= i /\ i<=3 ==> x$i= y$i  `,REPEAT GEN_TAC THEN REWRITE_TAC[PAIR_EQ] THEN REWRITE_TAC[ARITH_RULE `1<=i /\ i<= 3 <=> i=1 \/ i=2 \/ i=3`] THEN MESON_TAC[]);;

let int_ball_subset_CROSS=prove(`! (x:real^3) (r:real). INJ vector_to_pair (int_ball x r) (int_interval (x$1 - r)  (x$1 + r) CROSS (int_interval (x$2 - r)  (x$2 + r)) CROSS (int_interval (x$3 - r)  (x$3 + r)))`,REPEAT GEN_TAC THEN REWRITE_TAC[INJ] THEN REWRITE_TAC[lm2] THEN REWRITE_TAC[vector_to_pair] THEN REPEAT GEN_TAC THEN REWRITE_TAC[CART_EQ;DIMINDEX_3;trip_eq] THEN MESON_TAC[]);;


let FINITE_IMAGE_INJ=prove(`! (h:real^3->B) (s:real^3 ->bool) t. (!(x:real^3). x IN s ==> h x IN t) /\ INJ h s t /\ FINITE t ==> FINITE s`,
REPEAT GEN_TAC THEN REWRITE_TAC[INJ] THEN SIMP_TAC[MESON[] `p /\ (p /\ q) /\ w <=> p /\ q /\ w`] THEN STRIP_TAC
  THEN SUBGOAL_THEN `s= { x:real^3 | x IN s /\ (h:real^3->B) x IN t}` ASSUME_TAC
THENL [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ];ASM_MESON_TAC[FINITE_IMAGE_INJ_GENERAL]]
       THEN REWRITE_TAC[SET_RULE `{x | x IN s /\ (h:real^3->B) x IN t} SUBSET s`] THEN REWRITE_TAC[SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]);;

let finite_cross_int_interval=prove(`!(x:real^3) (r:real). FINITE (int_interval (x$1 - r)  (x$1 + r) CROSS (int_interval (x$2 - r)  (x$2 + r)) CROSS (int_interval (x$3 - r)  (x$3 + r)))`,REPEAT GEN_TAC THEN MESON_TAC[finite_int_interval;FINITE_CROSS]);;

(*----------------------------------------------------------*)
(*        Finiteness of integer points in a ball            *)
(*----------------------------------------------------------*)


let finite_int_ball=prove(`!(x:real^3) (r:real). FINITE (int_ball x r)`,REPEAT GEN_TAC THEN MATCH_MP_TAC(ISPECL [`vector_to_pair: real^3 -> real#real#real`; `(int_ball (x:real^3) (r:real)):real^3 -> bool`; `(int_interval ((x:real^3)$1 - r:real)  (x$1 + r) CROSS (int_interval (x$2 - r)  (x$2 + r)) CROSS (int_interval (x$3 - r)  (x$3 + r))):real#real#real -> bool`] FINITE_IMAGE_INJ) THEN SIMP_TAC[SPECL [`x:real^3`;`r:real`;`x':real^3`] lm2;finite_cross_int_interval;int_ball_subset_CROSS]);;

(*----------------------------------------------------------*)
(*                      Needed lemmas                       *)
(*----------------------------------------------------------*)

let disjoint_line_interval=prove(`!(x:real) (y:real). is_int x /\ is_int y /\ (? (z:real). x< z /\ z< x+ &1 /\ y<z /\ z< y+ &1) ==> x= y`,
REPEAT GEN_TAC THEN SIMP_TAC[GSYM INTEGER_IS_INT] THEN REPEAT STRIP_TAC THEN MP_TAC(SPECL [`x:real`;`y:real`] REAL_LE_CASES_INTEGERS)
  THEN ASM_SIMP_TAC[] THEN ASM_SIMP_TAC[SPECL [`x:real`;`y:real`] REAL_LE_INTEGERS] THEN SIMP_TAC[MESON[] `(((P\/Q)\/R ==> P) <=> (Q\/R ==> P))`]
  THEN STRIP_TAC
THENL [UNDISCH_TAC `(y:real <z):bool` THEN UNDISCH_TAC `(z:real< x+ &1):bool`;UNDISCH_TAC `(x:real <z):bool` THEN UNDISCH_TAC `(z:real< y+ &1):bool`]
THENL [REWRITE_TAC[MESON[] `P ==> Q ==> R <=> Q /\ P  ==> R`] THEN DISCH_TAC THEN MP_TAC(REAL_ARITH ` (y:real) < z /\ (z:real) < x+ &1   ==> y< x+ &1 `);REWRITE_TAC[MESON[] `P ==> Q ==> R <=> Q /\ P  ==> R`] THEN DISCH_TAC THEN MP_TAC(REAL_ARITH ` (x:real) < z /\ (z:real) < y+ &1   ==> x< y+ &1 `)]
THENL [ASM_SIMP_TAC[];ASM_SIMP_TAC[]]
THENL [UNDISCH_TAC `(x + &1 <= y:real):bool` THEN REWRITE_TAC[MESON[] `P ==> Q ==> R <=> Q /\ P  ==> R`];UNDISCH_TAC `(y + &1 <= x:real):bool` THEN REWRITE_TAC[MESON[] `P ==> Q ==> R <=> Q /\ P  ==> R`]]
THENL [MESON_TAC[REAL_ARITH `a:real < b /\ b<= a ==> F`];MESON_TAC[REAL_ARITH `a:real < b /\ b<= a ==> F`]]);;

let vector_eq2=prove(`!(x:real^3) (y:real^3). (!i. 1 <= i /\ i <= 3 ==> x$i = y$i) ==> x = y `,SIMP_TAC[CART_EQ;DIMINDEX_3]);;

let nonempty_cube=prove(`!(x:real^3). ~ (cube x= {})`,GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY]
			  THEN EXISTS_TAC `(lambda i. (x:real^3)$i + &1/ &2):real^3` 
THEN REWRITE_TAC[cube;IN_ELIM_THM] THEN GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA;DIMINDEX_3] THEN REAL_ARITH_TAC);;


let disjoint_cube=prove(`!(x:real^3) (y:real^3).(!i. 1<=i /\ i<=3 ==> is_int (x$i) /\ is_int (y$i))
 ==> ( ~(DISJOINT (cube x) (cube y)) <=> x = y)`, REPEAT STRIP_TAC THEN EQ_TAC
THENL [REWRITE_TAC[DISJOINT;SET_RULE `~ ((B:real^3 -> bool)= {}) <=> ?(x:real^3). x IN B`];SIMP_TAC[]]
THENL [DISCH_TAC THEN FIRST_X_ASSUM(CHOOSE_TAC);REWRITE_TAC[DISJOINT]]
THENL [UNDISCH_TAC `(x' IN cube (x:real^3) INTER cube y):bool`;SIMP_TAC[INTER_ACI;nonempty_cube]]
       THEN REWRITE_TAC[IN_INTER;IN_ELIM_THM;cube] THEN 
UNDISCH_TAC `(!i. 1 <= i /\ i <= 3 ==> is_int ((x:real^3)$i) /\ is_int ((y:real^3)$i)):bool`
	 THEN SIMP_TAC[FORALL_3] THEN REWRITE_TAC[MESON[] `P ==> Q ==> R <=> P /\ Q  ==> R`]
	 THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC (SPECL [`x:real^3`;`y:real^3`] vector_eq2)
	 THEN REWRITE_TAC[FORALL_3] THEN ASM_MESON_TAC[disjoint_line_interval]);;


(*-----------------------------------------------------------*)
(*      Bijectivity of map from int_ball to set_of_cube      *)
(*-----------------------------------------------------------*)


let inj_map0=prove(`! (x:real^3) (r:real). INJ map0 (int_ball x r) (set_of_cube (int_ball x r))`,
		   REWRITE_TAC[INJ;map0;set_of_cube] 
		     THEN SIMP_TAC[SET_RULE `x' IN int_ball x r ==> cube x' IN {cube x' | x' IN int_ball x r}`]
		     THEN REPEAT GEN_TAC THEN REWRITE_TAC[int_ball]
		     THEN REWRITE_TAC[IN_INTER;IN_ELIM_THM] THEN REPEAT STRIP_TAC
		     THEN ASM_SIMP_TAC[GSYM (SPECL [`x':real^3`;`y:real^3`] disjoint_cube)]
		     THEN REWRITE_TAC[DISJOINT;INTER_ACI;nonempty_cube]);;

let surj_map0=prove(`! (x:real^3) (r:real). SURJ map0 (int_ball x r) (set_of_cube (int_ball x r))`,
REWRITE_TAC[SURJ] THEN REWRITE_TAC[map0;set_of_cube] 
THEN SIMP_TAC[SET_RULE `x' IN int_ball x r ==> cube x' IN {cube x' | x' IN int_ball x r}`]
  THEN REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC
  THEN EXISTS_TAC `x'':real^3` THEN ASM_MESON_TAC[]);;


let bij_map0=prove(`! (x:real^3) (r:real). BIJ map0 (int_ball x r) (set_of_cube (int_ball x r))`,
MESON_TAC[BIJ;inj_map0;surj_map0]);;


(*-----------------------------------------------------------*)

let surj2_map0=prove(`!(x:real^3) (r:real). IMAGE map0 (int_ball x r) = set_of_cube (int_ball x r)`,
REWRITE_TAC[IMAGE] THEN REWRITE_TAC[map0] THEN REWRITE_TAC[set_of_cube] THEN SIMP_TAC[EXTENSION] 
THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[GSYM EXTENSION]);;



let int_ball_card_eq=prove(`!(x:real^3) (r:real). CARD (int_ball x r)= CARD (set_of_cube (int_ball x r))`,
REPEAT GEN_TAC THEN SIMP_TAC[GSYM (SPECL [`X:real^3`;`r:real` ] surj2_map0)]
  THEN MP_TAC(SPECL [`x:real^3`;`r:real`] finite_int_ball) THEN MP_TAC(SPECL [`x:real^3`;`r:real`] inj_map0)
  THEN REWRITE_TAC[MESON[] `a==>b==>c <=> a/\ b ==>c`;INJ] 
  THEN SIMP_TAC[set_of_cube;map0;SET_RULE `x' IN int_ball x r ==> cube x' IN {cube x' | x' IN int_ball x r}`]
  THEN REWRITE_TAC[MESON[map0] `cube (x':real^3)= map0 x'`;GSYM map0]
  THEN MESON_TAC[ISPECL [`map0:real^3 -> real^3 -> bool`;`(int_ball x r):real^3 -> bool`] CARD_IMAGE_INJ]);;



let cube_eq_interval=prove(`!(x:real^3). cube x= interval(x,x+ lambda i. &1)`,
GEN_TAC THEN REWRITE_TAC[EXTENSION;cube;interval;DIMINDEX_3] THEN SIMP_TAC[IN_ELIM_THM;LAMBDA_BETA;DIMINDEX_3]
  THEN SIMP_TAC[VECTOR_ADD_COMPONENT;LAMBDA_BETA;DIMINDEX_3]);;

let measurable_cube=prove( `!(x:real^3). measurable (cube x)`,REWRITE_TAC[cube_eq_interval;MEASURABLE_INTERVAL]);;

let finite_set_of_cube=prove(`!(x:real^3)(r:real). FINITE (set_of_cube (int_ball x r))`,
MESON_TAC[ISPECL [`map0:real^3 -> real^3 -> bool`; `(int_ball x r):real^3 -> bool`] FINITE_IMAGE;finite_int_ball;surj2_map0]);;

let MEASURABLE_UNIONS2 = prove
 (`!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> measurable s)
        ==> measurable (UNIONS f)`,
(*    GEN_TAC THEN *)REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[UNIONS_0; UNIONS_INSERT; MEASURABLE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_UNION THEN ASM_SIMP_TAC[]);;

let measurable_unions_cube=prove( `!(x:real^3)(r:real). measurable (UNIONS (set_of_cube (int_ball x r)))`,
REPEAT GEN_TAC THEN MATCH_MP_TAC(ISPEC `set_of_cube (int_ball x r):(real^3 -> bool) -> bool` MEASURABLE_UNIONS2) THEN REWRITE_TAC[finite_set_of_cube] THEN REWRITE_TAC[set_of_cube;IN_ELIM_THM] THEN MESON_TAC[measurable_cube]);;

let non_empty_cinterval=prove(`!(x:real^3). ~ (interval[x,x+ (lambda i. &1)]= {})`,
GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(lambda i. ((x:real^3)$i+ &1/ &2)):real^3`
  THEN REWRITE_TAC[interval;IN_ELIM_THM;LAMBDA_BETA;DIMINDEX_3]
  THEN GEN_TAC THEN DISCH_TAC THEN ASM_SIMP_TAC[VECTOR_ADD_COMPONENT;LAMBDA_BETA;DIMINDEX_3]
  THEN REAL_ARITH_TAC);;

(* in line 997 changed t to emoi, esusick 11/12 *)
let product_3=prove(`!(f:num -> real). product (1..3) f= f 1 * f 2 * f 3 `, let emoi= CONJUNCT2 PRODUCT_CLAUSES in 
GEN_TAC THEN MP_TAC(GSYM (SPECL [`1:num`;`3:num`] NUMSEG_RREC)) 
  THEN SIMP_TAC[ARITH_RULE `1<= 3`;ARITH_RULE `3-1 = 2`] 
  THEN REPEAT DISCH_TAC
  THEN MP_TAC(ISPECL [`3:num`;`f:num -> real`;`((1..2)):num ->bool`] emoi)
  THEN SIMP_TAC[MESON[NUMSEG_RREC;FINITE_NUMSEG] `FINITE (1..2)`]
  THEN SIMP_TAC[MESON[IN_NUMSEG;ARITH_RULE `~ (3<=2)`] ` ~( 3 IN (1..2))`] 
  THEN DISCH_TAC 
  THEN MP_TAC(GSYM (SPECL [`1:num`;`2:num`] NUMSEG_RREC)) 
  THEN SIMP_TAC[ARITH_RULE `1<=2`;ARITH_RULE `2-1=1`] 
  THEN MP_TAC(ISPECL [`2:num`;`f:num -> real`;`((1..1)):num ->bool`] emoi) 
  THEN SIMP_TAC[MESON[NUMSEG_RREC;FINITE_NUMSEG] `FINITE (1..1)`] 
  THEN SIMP_TAC[MESON[IN_NUMSEG;ARITH_RULE `~ (2<=1)`] ` ~( 2 IN (1..1))`]
  THEN SIMP_TAC[SPECL [`f : num -> real`;`1:num`] PRODUCT_SING_NUMSEG] THEN REAL_ARITH_TAC);;


(*------------------------------------------------------------------*)
(*            Measures of cube and union of cubes                   *)
(*------------------------------------------------------------------*)


let interval_upper_lowerbound=prove(`!(x:real^3). (interval_upperbound (interval [x,x + (lambda i. &1)])= x + (lambda i. &1)) /\ ( interval_lowerbound (interval [x,x + (lambda i. &1)])= x)`,
GEN_TAC 
THEN MP_TAC(ISPECL [`x:real^3`;`x + (lambda i. &1):real^3`] INTERVAL_UPPERBOUND) 
THEN MP_TAC(ISPECL [`x:real^3`;`x + (lambda i. &1):real^3`] INTERVAL_LOWERBOUND) 
THEN REWRITE_TAC[VECTOR_ADD_COMPONENT;DIMINDEX_3]
THEN SIMP_TAC[LAMBDA_BETA;DIMINDEX_3] 
THEN SIMP_TAC[REAL_ARITH `a:real <= a+ &1`]);;


let measure_cube=prove(`!(x:real^3). measure (cube x)= &1`,
REWRITE_TAC[cube_eq_interval]
THEN GEN_TAC 
THEN SIMP_TAC[MEASURE_INTERVAL] 
THEN REWRITE_TAC[content]
THEN SIMP_TAC[MESON[] `(if P then a else b) = &1 <=> if P then a= &1 else b= &1`]
THEN SIMP_TAC[COND_EXPAND] 
THEN SIMP_TAC[non_empty_cinterval;DIMINDEX_3]
THEN REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT;PRODUCT_CLAUSES;LAMBDA_BETA;DIMINDEX_3]
THEN SIMP_TAC[ISPEC `(\i. (interval_upperbound (interval [x,x + (lambda i. &1)]) - 
interval_lowerbound (interval [x,x + (lambda i. &1)]))$i):num -> real` product_3]
THEN SIMP_TAC[SPEC `x:real^3` interval_upper_lowerbound]
THEN SIMP_TAC[VECTOR_ARITH `((a:real^3) + b )- a = b`]
THEN SIMP_TAC[product_3]
THEN SIMP_TAC[LAMBDA_BETA;DIMINDEX_3;ARITH_RULE `1<= 1 /\ 1<= 3/\ 1<= 2 /\ 2<= 3 /\ 1<= 3 /\ 3<=3`]
THEN REAL_ARITH_TAC);;


let has_measure_cube=prove(`!(x:real^3)(r:real) (s:real^3 -> bool). s IN set_of_cube (int_ball x r) ==> s has_measure &1`,
REPEAT GEN_TAC THEN REWRITE_TAC[set_of_cube;IN_ELIM_THM] THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN ASM_MESON_TAC[measurable_cube;measure_cube;HAS_MEASURE_MEASURABLE_MEASURE]);;

(*Negligiblity of intersection of cubes *)

let negligible_cube=prove( `!(x:real^3)(r:real) (s:real^3 ->bool) (t:real^3 ->bool). s IN set_of_cube (int_ball x r) /\ t IN set_of_cube (int_ball x r) /\ ~(s = t) 
==> negligible (s INTER t)`,REPEAT GEN_TAC THEN REWRITE_TAC[set_of_cube;IN_ELIM_THM]
  THEN REPEAT STRIP_TAC THEN UNDISCH_TAC `(~ ((s:real^3 -> bool) = t)):bool` THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC THEN MP_TAC(MESON[] ` (x':real^3 = x'') ==> (cube x'= cube x'')`)
  THEN ONCE_REWRITE_TAC[MESON[] `(A ==> B) <=> (~B ==> ~A)`] THEN ASM_REWRITE_TAC[]
  THEN MP_TAC(MESON[int_ball;IN_INTER;IN_ELIM_THM] `x' IN int_ball x r /\ x'' IN int_ball x r ==> !i. 1 <= i /\ i <= 3 ==> is_int ((x')$i) /\ is_int ((x'')$i)`) THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC THEN MP_TAC(SPECL [`x':real^3`;`x'':real^3`] disjoint_cube) THEN ASM_REWRITE_TAC[]
THEN SIMP_TAC[DISJOINT;NEGLIGIBLE_EMPTY] THEN ONCE_REWRITE_TAC[MESON[] `( a<=>b ) <=> (b<=>a)`]
  THEN SIMP_TAC[NEGLIGIBLE_EMPTY;MESON[] `~ a ==> ~b <=> b==> a`]);;


let SUM_CONST2 = prove
 (`!c s. FINITE s ==> (sum s (\n. c) = &(CARD s) * c)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; CARD_CLAUSES; GSYM REAL_OF_NUM_SUC] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

(*There are two different theorems about SUM_CONST*)


let measure_unions_of_cube=prove( `!(x:real^3) (r:real). measure (UNIONS (set_of_cube (int_ball x r)))=   & (CARD (set_of_cube (int_ball x r)))`,REPEAT GEN_TAC THEN MP_TAC(ISPECL [`(\s. &1):(real^3 ->bool) ->real`;`set_of_cube (int_ball x r):(real^3 -> bool) -> bool`] MEASURE_NEGLIGIBLE_UNIONS)
    THEN SIMP_TAC[SPECL [`x:real^3`;`r:real`] finite_set_of_cube;ABS_SIMP;has_measure_cube]
    THEN REWRITE_TAC[SPECL [`x:real^3`;`r:real`] has_measure_cube]
    THEN REWRITE_TAC[SPECL [`x:real^3`;`r:real`] negligible_cube]
    THEN SIMP_TAC[] THEN DISCH_TAC THEN MP_TAC(SPECL [`x:real^3`;`r:real`] finite_set_of_cube) THEN REWRITE_TAC[REAL_ARITH `&(CARD (set_of_cube (int_ball x r)))= &(CARD (set_of_cube (int_ball x r)))* &1`]
    THEN MESON_TAC[ISPECL [`&1:real`;`set_of_cube (int_ball x r):(real^3 ->bool)-> bool`] SUM_CONST2;REAL_ARITH `&(CARD (set_of_cube (int_ball x r)))= &(CARD (set_of_cube (int_ball x r)))* &1`]);;

(*-----------------------------------------------------------------*)
(*             Union of cubes is contained in ball                 *)
(*-----------------------------------------------------------------*)


let pow_lesthan_1=prove( `!(a:real). &0 < a /\ a < &1 ==> a*a < &1`,REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:real`;`a:real`;`&1:real`] REAL_LT_LMUL) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_ARITH `(x:real)* &1= x`;REAL_ARITH `a:real <b /\ b< c ==> a< c`]);;


let cube_to_ball=prove(`!(x:real^3) (y:real^3). y IN cube x ==> norm (x-y)< sqrt(&3)`,
REPEAT STRIP_TAC  THEN MP_TAC(ISPEC `(x-y):real^3` NORM_POS_LE)
  THEN MP_TAC (SPEC `&3:real` SQRT_POS_LE) THEN ASM_REWRITE_TAC[REAL_ARITH `&0<= &3`;REAL_ARITH `&0<A ==> A= abs (A)`]
  THEN ONCE_REWRITE_TAC[GSYM REAL_ABS_REFL]
  THEN ONCE_REWRITE_TAC[MESON[] `a= b <=> b=a`]
  THEN REWRITE_TAC[MESON[] `((a:real) = b ==> (c:real) = d ==> c< a ) <=> ((a:real) = b ==> (c:real) = d ==> d< b )`]
  THEN REWRITE_TAC[REAL_LT_SQUARE_ABS] THEN SIMP_TAC[SQRT_POW_2; REAL_ARITH `&0<= &3`]
  THEN SIMP_TAC[NORM_POW_2;DOT_3] THEN REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN UNDISCH_TAC `(y IN cube (x:real^3)):bool`
  THEN REWRITE_TAC[cube;IN_ELIM_THM] THEN REWRITE_TAC[FORALL_3] 
  THEN REWRITE_TAC[REAL_ARITH `(a:real) <b /\ b< a+ &1 <=> &0< b-a /\ b-a < &1`]
  THEN ONCE_REWRITE_TAC[REAL_FIELD `((x:real^3)$1 - (y:real^3)$1) * (x$1 - y$1) +
     (x$2 - y$2) * (x$2 - y$2) +
     (x$3 - y$3) * (x$3 - y$3)= (y$1 - x$1) * (y$1 - x$1) +
     (y$2 - x$2) * (y$2 - x$2) +
     (y$3 - x$3) * (y$3 - x$3)`]
  THEN REPEAT STRIP_TAC THEN MP_TAC(MESON[pow_lesthan_1] `&0 < (y:real^3)$1 - (x:real^3)$1 /\ y$1 - x$1 < &1 ==> (y$1 - x$1) * (y$1 - x$1)< &1`)
  THEN ASM_REWRITE_TAC[]
  THEN MP_TAC(MESON[pow_lesthan_1] `&0 < (y:real^3)$2 - (x:real^3)$2 /\ y$2 - x$2 < &1 ==> (y$2 - x$2) * (y$2 - x$2)< &1`) THEN ASM_REWRITE_TAC[]
  THEN MP_TAC(MESON[pow_lesthan_1] `&0 < (y:real^3)$3 - (x:real^3)$3 /\ y$3 - x$3 < &1 ==> (y$3 - x$3) * (y$3 - x$3)< &1`) THEN ASM_REWRITE_TAC[]
  THEN MESON_TAC[REAL_ARITH `(a:real)< &1 /\ b< &1 /\c < &1 ==> a+b+c < &3`]);;


let unions_cube_subset_ball=prove(`!(x:real^3) (r:real). UNIONS (set_of_cube (int_ball x r)) SUBSET (hinhcau x (r+ sqrt (&3)))`,REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET;UNIONS]
    THEN GEN_TAC THEN REWRITE_TAC[hinhcau;IN_ELIM_THM]
    THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC
    THEN UNDISCH_TAC `(u IN set_of_cube (int_ball x r) /\ (x':real^3) IN u):bool`
    THEN REWRITE_TAC[set_of_cube] THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC
    THEN UNDISCH_TAC `((x':real^3) IN u):bool` THEN ASM_REWRITE_TAC[]
    THEN DISCH_TAC THEN MP_TAC(SPECL [`x'':real^3`;`x':real^3`] cube_to_ball) THEN ASM_REWRITE_TAC[]
    THEN UNDISCH_TAC `(x'' IN int_ball (x:real^3) r):bool`
    THEN REWRITE_TAC[int_ball;IN_INTER] THEN STRIP_TAC
    THEN MP_TAC(MESON[hinhcau;IN_ELIM_THM] `(x'':real^3) IN (hinhcau x r) ==> norm (x - x'') < r`) THEN ASM_REWRITE_TAC[]
    THEN ONCE_REWRITE_TAC[MESON[VECTOR_ARITH `(x:real^3)- x' = (x - x'') + (x'' - x')`] `norm ((x:real^3) - x') < r + sqrt (&3) <=> norm ((x - x'') + (x'' - x')) < r + sqrt (&3)`]
    THEN MESON_TAC[ISPECL [`(x - x''):real^3`;`(x'' - x'):real^3`] NORM_TRIANGLE;REAL_ARITH `((e:real) <= (a + c)) /\a <b /\ c< d ==> e < b+ d`]);;

(*-----------------------------------------------------------------*)


let hinhcau_ball=prove(`!(x:real^3)(r:real). hinhcau x r= ball (x,r)`,REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION;IN_ELIM_THM]
			 THEN REWRITE_TAC[hinhcau;ball;IN_ELIM_THM;dist]);;

let measure_unions_cube_less_ball=prove(`!(x:real^3)(r:real). measure (UNIONS (set_of_cube (int_ball x r))) 
<= measure (hinhcau x (r+ sqrt(&3)))`,REPEAT GEN_TAC THEN MP_TAC(SPECL [`x:real^3`;`r:real`] unions_cube_subset_ball) THEN MP_TAC(SPECL [`x:real^3`;`r:real`] measurable_unions_cube) THEN SIMP_TAC[SPECL [`x:real^3`;`r+ sqrt(&3):real`] hinhcau_ball]
  THEN MP_TAC(ISPECL [`x:real^3`;`r+ sqrt(&3):real`] MEASURABLE_BALL) THEN MESON_TAC[MEASURE_SUBSET]);;

let measure_hinhcau=prove(`!(x:real^3)(r:real). &0<= r ==> measure (hinhcau x r) = &4 / &3 * pi * (r pow 3)`,MESON_TAC[hinhcau_ball;VOLUME_BALL]);;


(*-----------------------------------------------------------------------*)
(*Lemma 2.14 [WQZISRI]:Upperbound for number of integer points in a ball *)
(*-----------------------------------------------------------------------*)

let WQZISRI=prove(`!(p:real^3)(r:real). &0<= r ==> FINITE (int_ball p r) /\ (& (CARD(int_ball p r)) 
<= (&4/ &3) * pi * ((r+ sqrt (&3)) pow 3))`,REPEAT GEN_TAC THEN SIMP_TAC[finite_int_ball]
		    THEN DISCH_TAC THEN MP_TAC(GSYM(SPECL [`p:real^3`;`r + sqrt (&3):real`] measure_hinhcau))
		    THEN MP_TAC(MESON[REAL_LE_RADD;REAL_ARITH `&0+ a= a`] `&0<= r ==> sqrt(&3)<= r+ sqrt(&3)`)
		    THEN ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `&3:real` SQRT_POS_LE) THEN REWRITE_TAC[REAL_ARITH `&0<= &3`]
		    THEN ONCE_REWRITE_TAC[MESON[] `a ==> b==>c ==> d <=> a/\b ==>c==>d`]
		    THEN DISCH_TAC THEN MP_TAC(REAL_ARITH `&0 <= sqrt (&3) /\ sqrt (&3) <= r + sqrt (&3) ==> &0<= r+ sqrt(&3)`) THEN ASM_REWRITE_TAC[]
		    THEN SIMP_TAC[] THEN SIMP_TAC[int_ball_card_eq] THEN SIMP_TAC[GSYM measure_unions_of_cube] THEN SIMP_TAC[measure_unions_cube_less_ball]);;


(*------------------------------------------------------------------------*)


let ccube=new_definition`ccube (x:real^3)={y :real^3 | !i. 1<= i /\ i<= 3 ==> x$i<= y$i /\ y$i <= x$i + &1}`;;

let set_of_ccube=new_definition`set_of_ccube(S:real^3 -> bool)= {ccube x| x IN S}`;;

let close_hinhcau=new_definition`close_hinhcau (x:real^3)(r:real)={ y:real^3 | norm (y-x)<= r}`;;

let map1=new_definition`map1 (x:real^3)= ccube x`;;


let daumut_ccube=prove(`!(x:real^3). x IN ccube x /\ (x + lambda i. &1) IN ccube x`,REWRITE_TAC[ccube;IN_ELIM_THM]
			THEN REWRITE_TAC[VECTOR_ADD_COMPONENT;LAMBDA_BETA;DIMINDEX_3]
			THEN SIMP_TAC[LAMBDA_BETA;DIMINDEX_3] THEN REAL_ARITH_TAC);;


let different_ccube=prove( `!(x:real^3) (y:real^3).((ccube x) = (ccube y) ==> x = y)`,
REPEAT STRIP_TAC THEN MP_TAC(SPEC `x:real^3` daumut_ccube) THEN ASM_REWRITE_TAC[]
  THEN REWRITE_TAC[ccube;VECTOR_ADD_COMPONENT;LAMBDA_BETA;DIMINDEX_3;IN_ELIM_THM]
  THEN SIMP_TAC[LAMBDA_BETA;DIMINDEX_3] THEN SIMP_TAC[REAL_ARITH `(a:real) + &1 <= b+ &1 <=> a <= b `]
  THEN REWRITE_TAC[FORALL_3] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC(SPECL [`x:real^3`;`y:real^3`] vector_eq2)
  THEN REWRITE_TAC[FORALL_3] THEN ASM_MESON_TAC[REAL_ARITH `(a:real)<= b /\ b<= a ==> a=b`]);;


let inj_map1=prove(`! (x:real^3) (r:real). INJ map1 (int_ball x r) (set_of_ccube (int_ball x r))`,
REWRITE_TAC[INJ;map1;set_of_ccube] THEN SIMP_TAC[SET_RULE `x' IN int_ball x r ==> ccube x' IN {ccube x' | x' IN int_ball x r}`] THEN REPEAT GEN_TAC THEN REWRITE_TAC[int_ball] THEN MESON_TAC[different_ccube]);;		     

let surj2_map1=prove(`!(x:real^3) (r:real). IMAGE map1 (int_ball x r) = set_of_ccube (int_ball x r)`,
REWRITE_TAC[IMAGE] THEN REWRITE_TAC[map1] THEN REWRITE_TAC[set_of_ccube] THEN SIMP_TAC[EXTENSION] 
THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[GSYM EXTENSION]);;

let int_ball_card_eq_ccube=prove(`!(x:real^3) (r:real). CARD (int_ball x r)= CARD (set_of_ccube (int_ball x r))`,
REPEAT GEN_TAC THEN SIMP_TAC[GSYM (SPECL [`X:real^3`;`r:real` ] surj2_map1)]
  THEN MP_TAC(SPECL [`x:real^3`;`r:real`] finite_int_ball) THEN MP_TAC(SPECL [`x:real^3`;`r:real`] inj_map1)
  THEN REWRITE_TAC[MESON[] `a==>b==>c <=> a/\ b ==>c`;INJ] 
  THEN SIMP_TAC[set_of_ccube;map1;SET_RULE `x' IN int_ball x r ==> ccube x' IN {ccube x' | x' IN int_ball x r}`]
  THEN REWRITE_TAC[MESON[map1] `ccube (x':real^3)= map1 x'`;GSYM map1]
  THEN MESON_TAC[ISPECL [`map1:real^3 -> real^3 -> bool`;`(int_ball x r):real^3 -> bool`] CARD_IMAGE_INJ]);;

let ccube_eq_interval=prove(`!(x:real^3). ccube x= interval[x,x+ lambda i. &1]`,
GEN_TAC THEN REWRITE_TAC[EXTENSION;ccube;interval;DIMINDEX_3] THEN SIMP_TAC[IN_ELIM_THM;LAMBDA_BETA;DIMINDEX_3]
  THEN SIMP_TAC[VECTOR_ADD_COMPONENT;LAMBDA_BETA;DIMINDEX_3]);;


let measurable_ccube=prove( `!(x:real^3). measurable (ccube x)`,REWRITE_TAC[ccube_eq_interval;MEASURABLE_INTERVAL]);;

let finite_set_of_ccube=prove(`!(x:real^3)(r:real). FINITE (set_of_ccube (int_ball x r))`,
MESON_TAC[ISPECL [`map1:real^3 -> real^3 -> bool`; `(int_ball x r):real^3 -> bool`] FINITE_IMAGE;finite_int_ball;surj2_map1]);;



let measurable_unions_ccube=prove( `!(x:real^3)(r:real). measurable (UNIONS (set_of_ccube (int_ball x r)))`,
REPEAT GEN_TAC THEN MATCH_MP_TAC(ISPEC `set_of_ccube (int_ball x r):(real^3 -> bool) -> bool` MEASURABLE_UNIONS2) 
THEN REWRITE_TAC[finite_set_of_ccube] THEN REWRITE_TAC[set_of_ccube;IN_ELIM_THM] THEN MESON_TAC[measurable_ccube]);;


let measure_ccube=prove(`!(x:real^3). measure (ccube x)= &1`,REWRITE_TAC[ccube_eq_interval]
 THEN GEN_TAC THEN SIMP_TAC[MEASURE_INTERVAL] THEN REWRITE_TAC[content]
			 THEN SIMP_TAC[MESON[] `(if P then a else b) = &1 <=> if P then a= &1 else b= &1`]
 THEN SIMP_TAC[COND_EXPAND] THEN SIMP_TAC[non_empty_cinterval;DIMINDEX_3]
			 THEN REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT;PRODUCT_CLAUSES;LAMBDA_BETA;DIMINDEX_3]
 THEN SIMP_TAC[ISPEC `(\i. (interval_upperbound (interval [x,x + (lambda i. &1)]) - 
interval_lowerbound (interval [x,x + (lambda i. &1)]))$i):num -> real` product_3]
 THEN SIMP_TAC[SPEC `x:real^3` interval_upper_lowerbound]
					 THEN SIMP_TAC[VECTOR_ARITH `((a:real^3) + b )- a = b`]
					 THEN SIMP_TAC[product_3]
 THEN SIMP_TAC[LAMBDA_BETA;DIMINDEX_3;ARITH_RULE `1<= 1 /\ 1<= 3/\ 1<= 2 /\ 2<= 3 /\ 1<= 3 /\ 3<=3`]
					 THEN REAL_ARITH_TAC);;


let has_measure_ccube=prove(`!(x:real^3)(r:real) (s:real^3 -> bool). s IN set_of_ccube (int_ball x r) ==> s has_measure &1`,
REPEAT GEN_TAC THEN REWRITE_TAC[set_of_ccube;IN_ELIM_THM] THEN DISCH_TAC THEN FIRST_X_ASSUM CHOOSE_TAC THEN ASM_MESON_TAC[measurable_ccube;measure_ccube;HAS_MEASURE_MEASURABLE_MEASURE]);;


let measure_element_set_ccube=prove( `! (S:real^3 -> bool) (t:real^3 -> bool). t IN (set_of_ccube S) ==> measure t= &1`,
REPEAT GEN_TAC THEN REWRITE_TAC[set_of_ccube;IN_ELIM_THM]THEN MESON_TAC[measure_ccube]);;

let sum_measure_ccube=prove(`!(p:real^3)(r:real). sum (set_of_ccube (int_ball p r)) (\s. measure s)= &(CARD (set_of_ccube (int_ball p r)))`,REPEAT GEN_TAC
			      THEN MP_TAC(ISPECL [`(\s. measure s):(real^3-> bool)-> real`;`(\s. &1):(real^3-> bool)-> real`;`set_of_ccube (int_ball p r):(real^3->bool) -> bool`] SUM_EQ)
			      THEN REWRITE_TAC[IN_ELIM_THM]
			      THEN REWRITE_TAC[measure_element_set_ccube]
			      THEN REWRITE_TAC[MESON[] `a=b ==> a=c <=> a=b ==> b=c`]
			      THEN MP_TAC(SPECL [`p:real^3`;`r:real`] finite_set_of_ccube)
			      THEN MESON_TAC[ISPECL [`&1:real`;`set_of_ccube (int_ball x r):(real^3 ->bool)-> bool`] SUM_CONST;REAL_ARITH `&(CARD (set_of_ccube (int_ball x r)))= &(CARD (set_of_ccube (int_ball x r)))* &1`]);;

(* There are two different theorems about SUM_EQ and sum *)


let mea_unions_ccube_le_card=prove(`!(x:real^3) (r:real). measure (UNIONS (set_of_ccube (int_ball x r)))<=   & (CARD (set_of_ccube (int_ball x r)))`,REPEAT GEN_TAC THEN MP_TAC(ISPEC  `set_of_ccube (int_ball x r):(real^3 -> bool) -> bool` MEASURE_UNIONS_LE) THEN SIMP_TAC[SPECL [`x:real^3`;`r:real`] finite_set_of_ccube;ABS_SIMP;has_measure_ccube]
				     THEN REWRITE_TAC[set_of_ccube;IN_ELIM_THM]
				     THEN REWRITE_TAC[MESON[measurable_ccube] `!s. (?x'. x' IN int_ball x r /\ s = ccube x') ==> measurable s`] THEN REWRITE_TAC[GSYM set_of_ccube] THEN MESON_TAC[SPECL [`x:real^3`;`r:real`] sum_measure_ccube]);;

let in_ccube_floor=prove(`!(x:real^3). x IN ccube (lambda i. floor (x$i)) `,GEN_TAC THEN REWRITE_TAC[ccube;IN_ELIM_THM]
			   THEN GEN_TAC THEN SIMP_TAC[LAMBDA_BETA;DIMINDEX_3]
			   THEN REWRITE_TAC[FLOOR] THEN MESON_TAC[FLOOR;REAL_ARITH `(a:real) < b ==> a<= b`]);;
REAL_LE_SQUARE_ABS;;
REAL_ABS_REFL;;

let pow_lesthan_eq_1=prove( `!(a:real). &0 <= a /\ a <= &1 ==> a*a <= &1`,REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:real`;`a:real`;`&1:real`] REAL_LE_LMUL) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_ARITH `(x:real)* &1= x`;REAL_ARITH `a:real <=b /\ b<= c ==> a<= c`]);;

let ccube_to_ball=prove(`!(x:real^3) (y:real^3). y IN ccube x ==> norm (x-y)<= sqrt(&3)`,
REPEAT STRIP_TAC  THEN MP_TAC(ISPEC `((x:real^3)-y):real^3` NORM_POS_LE)
  THEN MP_TAC (SPEC `&3:real` SQRT_POS_LE) THEN ASM_REWRITE_TAC[REAL_ARITH `&0<= &3`;REAL_ARITH `&0<A ==> A= abs (A)`]
  THEN ONCE_REWRITE_TAC[GSYM REAL_ABS_REFL]
  THEN ONCE_REWRITE_TAC[MESON[] `(a:real)= b <=> b=a`]
  THEN REWRITE_TAC[MESON[] `((a:real) = b ==> (c:real) = d ==> c<= a ) <=> ((a:real) = b ==> (c:real) = d ==> d<= b )`]
  THEN REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN SIMP_TAC[SQRT_POW_2; REAL_ARITH `&0<= &3`]
  THEN SIMP_TAC[NORM_POW_2;DOT_3] THEN REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN UNDISCH_TAC `(y IN ccube (x:real^3)):bool`
  THEN REWRITE_TAC[ccube;IN_ELIM_THM] THEN REWRITE_TAC[FORALL_3]
  THEN REWRITE_TAC[REAL_ARITH `(a:real) <=b /\ b<= a+ &1 <=> &0<= b-a /\ b-a <= &1`]
  THEN ONCE_REWRITE_TAC[REAL_FIELD `((x:real^3)$1 - (y:real^3)$1) * (x$1 - y$1) +
     (x$2 - y$2) * (x$2 - y$2) +
     (x$3 - y$3) * (x$3 - y$3)= (y$1 - x$1) * (y$1 - x$1) +
     (y$2 - x$2) * (y$2 - x$2) +
     (y$3 - x$3) * (y$3 - x$3)`]
  THEN REPEAT STRIP_TAC THEN MP_TAC(MESON[pow_lesthan_eq_1] `&0 <= (y:real^3)$1 - (x:real^3)$1 /\ y$1 - x$1 <= &1 ==> (y$1 - x$1) * (y$1 - x$1)<= &1`)
  THEN ASM_REWRITE_TAC[]
  THEN MP_TAC(MESON[pow_lesthan_eq_1] `&0 <= (y:real^3)$2 - (x:real^3)$2 /\ y$2 - x$2 <= &1 ==> (y$2 - x$2) * (y$2 - x$2)<= &1`) THEN ASM_REWRITE_TAC[]
  THEN MP_TAC(MESON[pow_lesthan_eq_1] `&0 <= (y:real^3)$3 - (x:real^3)$3 /\ y$3 - x$3 <= &1 ==> (y$3 - x$3) * (y$3 - x$3)<= &1`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[REAL_ARITH `(a:real)<= &1 /\ b<= &1 /\c <= &1 ==> a+b+c <= &3`]);;


let ball_subset_union_ccube=prove(`!(x:real^3) (r:real).ball(x,r- sqrt(&3)) SUBSET (UNIONS  (set_of_ccube (int_ball x r)))`,REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET;IN_ELIM_THM;UNIONS;set_of_ccube]
   THEN GEN_TAC THEN REWRITE_TAC[ball;IN_ELIM_THM]
   THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN EXISTS_TAC `ccube (lambda i. (floor (((x':real^3))$i)):real):real^3 ->bool`
   THEN REWRITE_TAC[SPEC `x':real^3` in_ccube_floor]
				   THEN EXISTS_TAC `(lambda i. (floor ((x':real^3)$i)):real):real^3`
				   THEN SIMP_TAC[] THEN REWRITE_TAC[int_ball;IN_ELIM_THM]
				   THEN REWRITE_TAC[IN_INTER;IN_ELIM_THM]
				   THEN SIMP_TAC[LAMBDA_BETA;DIMINDEX_3;hinhcau;IN_ELIM_THM;FLOOR]
				   THEN REWRITE_TAC[FLOOR;GSYM INTEGER_IS_INT]
				   THEN REWRITE_TAC[MESON[VECTOR_ARITH `(x:real^3) - (lambda i. floor ((x':real^3)$i))= (x- x') + (x' - (lambda i. floor (x'$i)))`] `(norm:real^3 ->real) ((x:real^3) - (lambda i. (floor ((x':real^3)$i)):real))= norm ((x- x') + (x' - (lambda i. floor (x'$i))))`]
				   THEN MP_TAC(SPECL [`(lambda i. (floor ((x':real^3)$i)):real):real^3`;`x':real^3`] ccube_to_ball)
				   THEN SIMP_TAC[SPEC `x':real^3` in_ccube_floor]
				   THEN UNDISCH_TAC `((norm:real^3 ->real) ((x:real^3) - x') < (r:real) - sqrt (&3)):bool`
				   THEN MP_TAC(ISPECL [`x - (x':real^3)`; ` x' - (lambda i. (floor ((x':real^3)$i):real)):real^3`] NORM_TRIANGLE)
				   THEN ONCE_REWRITE_TAC[MESON[] `a ==>b ==> c ==> d <=> a/\b/\c ==>  d`]
				   THEN MESON_TAC[NORM_SUB;REAL_ARITH `a:real <= b+ c /\ b< r- sqrt(&3) /\ c<= sqrt (&3) ==> a< r`]);;


let volume_ball_gon=prove( `!(x:real^3)(r:real). sqrt(&3) <= r ==> measurable (ball(x,r- sqrt(&3))) /\ measure (ball(x,r- sqrt(&3)))= (&4/ &3)* pi* (r- sqrt (&3)) pow 3`,ONCE_REWRITE_TAC[REAL_ARITH `a:real <=b <=> &0<= b-a`] THEN MESON_TAC[MEASURABLE_BALL;VOLUME_BALL]);;

let lower_bound_measure_unions_ccube=prove(`!(x:real^3)(r:real). (sqrt(&3)<= r) ==> (&4/ &3)* pi* (r- sqrt (&3)) pow 3 <= measure (UNIONS  (set_of_ccube (int_ball x r)))`,REPEAT STRIP_TAC THEN MP_TAC(ISPECL [`ball(x,r- sqrt(&3)):real^3 -> bool`;`UNIONS  (set_of_ccube (int_ball x r)):real^3 -> bool`] MEASURE_SUBSET) THEN ASM_REWRITE_TAC[volume_ball_gon; measurable_unions_ccube;ball_subset_union_ccube] THEN ASM_SIMP_TAC[volume_ball_gon]);;


(*-----------------------------------------------------------------------*)
(* Lemma 2.15 [PWVIIOL] lower bound for number of integer points in ball *)
(*-----------------------------------------------------------------------*)


let PWVIIOL=prove(`!(x:real^3)(r:real). (sqrt(&3) <= r) ==> FINITE (int_ball x r) /\  (&4/ &3)* pi* (r- sqrt (&3)) pow 3 <= &(CARD(int_ball x r))`,REPEAT STRIP_TAC THEN SIMP_TAC[finite_int_ball] THEN ASM_MESON_TAC[ int_ball_card_eq_ccube;mea_unions_ccube_le_card;lower_bound_measure_unions_ccube;REAL_ARITH `a:real <= b /\ b<= c ==> a<= c`]);;


(*-----------------------------------------------------------------------*)


let integer_point= new_definition`integer_point (S:real^3 -> bool)= {x:real^3 | (!i. 1<= i /\ i<=3 ==> is_int(x$i)) /\ x IN S}`;;

let int_ball_subset=prove( `!(x:real^3)(r1:real)(r2:real). r1< r2 ==> (int_ball x r1) SUBSET (int_ball x r2)`,REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET;int_ball;IN_INTER;IN_ELIM_THM] THEN GEN_TAC THEN SIMP_TAC[]
			     THEN REWRITE_TAC[hinhcau;IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_ARITH `a:real< b /\ b< c ==> a< c`]);;

let card_int_ball_ineq=prove(`!(x:real^3)(r1:real)(r2:real). r1< r2 ==> CARD (int_ball x r1)<= CARD (int_ball x r2)`,MESON_TAC[int_ball_subset;finite_int_ball;CARD_SUBSET]);;


let eq_def_intball=prove( `!(x:real^3)(k1:real)(k2:real)(r:real).(&0< k1 /\ &0< k2 /\ k2<= r) ==> integer_point (ball(x,r+ k1) DIFF ball(x,r- k2)) = (int_ball x (r+ k1)) DIFF (int_ball x (r- k2))`,REPEAT STRIP_TAC
			    THEN REWRITE_TAC[EXTENSION;integer_point;DIFF;ball;int_ball;IN_ELIM_THM]
			    THEN GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[dist;IN_INTER;IN_ELIM_THM]
			    THEN REWRITE_TAC[hinhcau;IN_ELIM_THM;MESON[] `~ (A /\ B ) <=> ~A \/ ~B`]
			    THEN MESON_TAC[]);;

let card_int_ball_le=prove( `!(x:real^3)(k1:real)(k2:real)(r:real).(&0<k1 /\ &0<k2 /\ k2+ sqrt(&3)<= r) ==> &(CARD (int_ball x (r + k1))) <=
     &4 / &3 * pi * ((r + k1) + sqrt (&3)) pow 3`,REPEAT STRIP_TAC THEN MP_TAC(SPECL [`x:real^3`;`r+ k1:real`] WQZISRI) THEN MP_TAC(REAL_ARITH `&0<k1 /\ &0<k2 /\ k2+ sqrt(&3)<= r ==> sqrt(&3)< r+k1`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC(MESON[SPEC `&3:real` SQRT_POS_LE;REAL_ARITH `&0 <= &3`] `&0<= sqrt(&3)`) THEN DISCH_TAC THEN MP_TAC(REAL_ARITH `&0 <= sqrt (&3) /\ (sqrt (&3) < r + k1) ==> &0<= r+ k1`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let card_int_ball_le2=prove( `!(x:real^3)(k1:real)(r:real).(&0<=k1 /\ &0<= r) ==> &(CARD (int_ball x (r + k1))) <=
     &4 / &3 * pi * ((r + k1) + sqrt (&3)) pow 3`,REPEAT STRIP_TAC THEN MP_TAC(SPECL [`x:real^3`;`r+ k1:real`] WQZISRI) THEN MP_TAC(REAL_ARITH `&0<=k1 /\ &0<= r ==> &0<= r+k1`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;


let card_int_ball_pos=prove(`!(x:real^3)(k1:real)(k2:real)(r:real).(&0<k1 /\ &0<k2 /\ k2+ sqrt(&3)<= r) ==> &4 / &3 * pi * ((r - k2) - sqrt (&3)) pow 3 <= &(CARD (int_ball x (r - k2)))`,REPEAT STRIP_TAC THEN MP_TAC(SPECL [`x:real^3`;`r- k2:real`] PWVIIOL) THEN MP_TAC(REAL_ARITH `k2 + sqrt (&3) <= r ==> sqrt(&3)<= r- k2`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let bdt1_finiteness=prove(`!(r:real)(k:real). &0<r ==> &4*pi*r*k <= &4*pi*r* abs k`,REPEAT STRIP_TAC
			    THEN ASSUME_TAC PI_POS THEN MP_TAC(MESON[REAL_LT_LMUL;REAL_ARITH `&0* r= &0`;REAL_ARITH `pi* r= r* pi`;REAL_ARITH `&0< e ==> &0< &4* e`] `&0< r /\ &0< pi ==> &0< &4*pi*r`) THEN ASM_REWRITE_TAC[]
			    THEN REWRITE_TAC[REAL_ARITH `(a:real) *b*C*d= (a*b*C)*d`]
			    THEN MP_TAC(SPEC `k:real` REAL_ABS_LE) THEN MESON_TAC[REAL_ARITH `&0 < &4 * pi * r ==> &0<= &4 * pi * r`;REAL_LE_LMUL]);;


let bdt2_finiteness=prove( `!(r:real)(k:real)(i:num).(&0< k /\ k<= r ==> &1 <= r pow i / k pow i)`,REPEAT STRIP_TAC
			     THEN MP_TAC(SPECL [`k:real`;`i:num`] REAL_POW_LT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
			     THEN ASM_SIMP_TAC[GSYM (ISPECL [`&1:real`;`(r pow i/ k pow i):real`;`(k pow i):real`] REAL_LE_RMUL_EQ)] THEN MP_TAC(REAL_ARITH ` &0 < k pow i ==> ~ (&0= k pow i)`) THEN ASM_REWRITE_TAC[] 
			     THEN SIMP_TAC[REAL_DIV_RMUL] THEN ASM_SIMP_TAC[REAL_ARITH ` &1 * a= a`;REAL_ARITH `a< b ==> a<= b`] THEN ASM_MESON_TAC[REAL_POW_LE2;REAL_ARITH `&0< k ==> &0 <= k`]);;


let bdt3_finiteness=prove( `!(r:real)(k1:real)(k2:real) (k:real). ( &0 < r/\ &0 < k1 /\ &0< k2) ==>( &0<=  &4 * pi *r* (abs k) /\ &0 <= &4/ &3 *pi*( (k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3))`,
			   REPEAT STRIP_TAC THENL [ASM_MESON_TAC[REAL_ARITH `&0< A==> &0<= A`;PI_POS_LE;REAL_ABS_POS;REAL_LE_MUL;REAL_ARITH `&0<= &4`];MP_TAC(MESON[REAL_ARITH `&0< k1 ==> sqrt(&3)<= k1 + sqrt(&3)`;SQRT_POS_LE;REAL_ARITH `&0<= &3`;REAL_ARITH `a<= b /\ b<=c ==> a<= c`]  `&0< k1 ==> &0<= k1 + sqrt (&3)`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC(MESON[REAL_ARITH `&0< k2 ==> sqrt(&3)<= k2 + sqrt(&3)`;SQRT_POS_LE;REAL_ARITH `&0<= &3`;REAL_ARITH `a<= b /\ b<=c ==> a<= c`]  `&0< k2 ==> &0<= k2 + sqrt (&3)`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC(SPECL [`k1 + sqrt (&3):real`;` 3:num`] REAL_POW_LE) THEN ASM_REWRITE_TAC[]
			     THEN MP_TAC(SPECL [`k2 + sqrt (&3):real`;` 3:num`] REAL_POW_LE) THEN ASM_REWRITE_TAC[]
			     THEN REPEAT DISCH_TAC THEN MP_TAC(REAL_ARITH `&0 <= (k2 + sqrt (&3)) pow 3 /\ &0 <= (k1 + sqrt (&3)) pow 3 ==> &0<=  (k1 + sqrt (&3)) pow 3+ (k2 + sqrt (&3)) pow 3`) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[REAL_LE_MUL;REAL_ARITH `&0<= &4/ &3`;PI_POS_LE]]);;



let bdt4_finiteness = prove(`!(k1:real)(k2:real) (r:real). (&0< k1 /\ &0< k2 /\ k2 + sqrt (&3) <= r) ==> (&4 / &3 * pi * ((r + k1) + sqrt (&3)) pow 3)- (&4 / &3 * pi * (r - k2 - sqrt (&3)) pow 3)<= (&4/ &3* pi*( &3*(k1+ k2+ &2*sqrt(&3)) +((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3) /((k2 + sqrt (&3)) pow 2) + &3 * abs(((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2)) / (k2 + sqrt (&3)))) *r pow 2`, REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_FIELD `&4 / &3 * pi * ((r + k1) + sqrt (&3)) pow 3 -
 &4 / &3 * pi * (r - k2 - sqrt (&3)) pow 3= ( &4*pi*r pow 2 * (k1+k2+ &2*sqrt(&3)) + &4*pi*r* ((k1+ sqrt(&3))pow 2 - (k2+ sqrt(&3)) pow 2)+ &4/ &3*pi*((k1+ sqrt(&3))pow 3 + (k2+ sqrt(&3)) pow 3))`]
       THEN REWRITE_TAC[REAL_FIELD ` (&4/ &3 * pi*( &3* (k1+k2+ &2*sqrt(&3)) +
  ((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3) / ((k2 + sqrt (&3)) pow 2) +
  &3 *
  abs (((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2)) / (k2 + sqrt (&3)))) *
 r pow 2=  (&4 * pi * r pow 2 * (k1 + k2 + &2 * sqrt (&3))+ &4*pi*r pow 2* abs (((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2)) / (k2 + sqrt (&3))+ &4/ &3*pi* r pow 2* ((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3) / ((k2 + sqrt (&3)) pow 2))`]
 THEN REWRITE_TAC[REAL_ARITH `(a:real) + b+ c <= a + d + e <=> b+c <= d+ e`]
 THEN  MATCH_MP_TAC(REAL_ARITH `&4 * pi * r * ((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2)<=  &4 *
 pi *
 r pow 2 *
 abs ((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2) / (k2 + sqrt (&3)) /\  &4 / &3 * pi * ((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3)<=  &4 / &3 *
 pi *
 r pow 2 *
 ((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3) / ((k2 + sqrt (&3)) pow 2) ==> &4 * pi * r * ((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2) +
 &4 / &3 * pi * ((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3) <=
 &4 *
 pi *
 r pow 2 *
 abs ((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2) / (k2 + sqrt (&3)) +
 &4 / &3 *
 pi *
 r pow 2 *
 ((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3) / ((k2 + sqrt (&3)) pow 2)`)
 THEN MATCH_MP_TAC(REAL_ARITH `&4 * pi * r * ((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2) <= &4*pi* r  * abs ((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2)  /\ &4*pi* r  * abs ((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2)<=   &4 *
 pi *
 r pow 2 *
 abs ((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2) / (k2 + sqrt (&3)) /\ &4 / &3 * pi * ((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3) <=
 &4 / &3 *
 pi *
 r pow 2 *
 ((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3) / ((k2 + sqrt (&3)) pow 2) ==> &4 * pi * r * ((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2) <=
 &4 *
 pi *
 r pow 2 *
 abs ((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2) / (k2 + sqrt (&3)) /\
 &4 / &3 * pi * ((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3) <=
 &4 / &3 *
 pi *
 r pow 2 *
 ((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3) / ((k2 + sqrt (&3)) pow 2) `)
 THEN MP_TAC(MESON[REAL_ARITH `&0 < k2 /\ k2 + sqrt (&3) <= r ==> sqrt(&3)< r`;MESON[SQRT_POS_LT;REAL_ARITH `&0< &3`] `&0< sqrt( &3)`;REAL_ARITH `a:real <b/\ b< c ==> a< c`] `&0 < k2 /\ k2 + sqrt (&3) <= r ==> &0< r`)
 THEN ASM_SIMP_TAC[bdt1_finiteness] THEN DISCH_TAC THEN REWRITE_TAC[bdt1_finiteness] THEN MP_TAC(REAL_ARITH `&0< k2 ==> &0 <=k2`) THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_FIELD `&4 *
     pi *
     r pow 2 *
     abs
     ((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2) / (k2 + sqrt (&3))= ( &4*pi* r* abs
     ((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2))*(r/ (k2+ sqrt(&3)))`] THEN REWRITE_TAC[REAL_FIELD `&4 / &3 *
     pi *
     r pow 2 *
     ((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3) /
     ((k2 + sqrt (&3)) pow 2) = (&4 / &3 *
     pi *((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3))*(r pow 2/ ((k2 + sqrt (&3)) pow 2))`]
     THEN DISCH_TAC THEN MP_TAC(SPECL [`r:real`;`k2+ sqrt(&3):real`;`1:num`] bdt2_finiteness)
     THEN MP_TAC(MESON[MESON[SQRT_POS_LT;REAL_ARITH `&0< &3`] `&0< sqrt( &3)`;REAL_ARITH `&0 < k2 
==> sqrt(&3)< k2 + sqrt(&3)`;REAL_ARITH `a:real <b/\ b< c ==> a< c`] `&0 < k2 
==> &0< k2 + sqrt(&3)`) THEN  ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_ARITH `(x:real) pow 1= x`]
     THEN DISCH_TAC THEN MP_TAC(SPECL [`r:real`;`k2+ sqrt(&3):real`;`2:num`] bdt2_finiteness) THEN ASM_REWRITE_TAC[]
     THEN REPEAT DISCH_TAC THEN MP_TAC(SPECL [`r:real`;`k1:real`;`k2:real`;`((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2):real`] bdt3_finiteness) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[REAL_LE_LMUL;REAL_ARITH ` a* &1= a`]);;



let bdt5_finiteness=prove(`!(x:real^3)(k1:real)(k2:real) (r:real). (&0< k1 /\ &0< k2 /\ k2 + sqrt (&3) <= r) ==> ?(C:real). &(CARD ((int_ball x (r+ k1)) DIFF (int_ball x (r- k2))))<= C* r pow 2`,REPEAT STRIP_TAC THEN EXISTS_TAC `(&4 / &3 *
  pi *
  (&3 * (k1 + k2 + &2 * sqrt (&3)) +
   ((k1 + sqrt (&3)) pow 3 + (k2 + sqrt (&3)) pow 3) / (k2 + sqrt (&3)) pow 2 +
   &3 *
   abs ((k1 + sqrt (&3)) pow 2 - (k2 + sqrt (&3)) pow 2) / (k2 + sqrt (&3)))):real`
			    THEN MP_TAC(ISPECL [`int_ball x (r + k1):real^3 -> bool`;`int_ball x (r - k2):real^3 -> bool`] CARD_DIFF)
  THEN REWRITE_TAC[finite_int_ball] THEN MP_TAC(REAL_ARITH `&0<k1 /\ &0< k2 ==> r:real -k2 < r + k1`)
  THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[int_ball_subset]
  THEN DISCH_TAC THEN MP_TAC(SPECL [`x:real^3`;`r-k2:real`;`r+k1:real`] card_int_ball_ineq)
  THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REPEAT DISCH_TAC 
  THEN MP_TAC(SPECL [`x:real^3`;`k1:real`;`k2:real`;`r:real`] card_int_ball_le) THEN ASM_REWRITE_TAC[]
  THEN MP_TAC(SPECL [`x:real^3`;`k1:real`;`k2:real`;`r:real`] card_int_ball_pos) THEN ASM_REWRITE_TAC[]
  THEN MP_TAC(SPECL [`k1:real`;`k2:real`;`r:real`] bdt4_finiteness) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let card_diff_ineq=prove( `!(x:real^3)(k1:real)(k2:real) (r:real). CARD ((int_ball x (r+ k1)) DIFF (int_ball x (r- k2))) <= CARD (int_ball x (r+ k1))`,REPEAT GEN_TAC THEN ASSUME_TAC(SPECL [`x:real^3`;`r+ k1:real`] finite_int_ball) THEN ASM_MESON_TAC[CARD_SUBSET;SUBSET_DIFF]);;

let bdt6_finiteness=prove(`!(x:real^3)(k1:real)(k2:real) (r:real). (&0< k1 /\ &0<r) ==> &(CARD ((int_ball x (r+ k1)) DIFF (int_ball x (r- k2)))) <= &4/ &3*pi*(r+k1+ sqrt(&3))pow 3`,REPEAT STRIP_TAC THEN MP_TAC(GSYM (SPECL [`CARD (int_ball x (r + k1) DIFF int_ball x (r - k2)):num`;`CARD (int_ball x (r+ k1)):num`] REAL_OF_NUM_LE)) THEN SIMP_TAC[card_diff_ineq]
	    THEN MP_TAC(SPECL [`x:real^3`;`k1:real`;`r:real`] card_int_ball_le2) THEN ASM_SIMP_TAC[REAL_ARITH `&0< k1 /\ &0< r ==> &0<= k1 /\ &0<= r`] THEN ASM_SIMP_TAC[REAL_ARITH `&0< a ==> &0<= a`] THEN MESON_TAC[REAL_ARITH `a<= b /\ c<=a ==> c<= b`; REAL_ARITH `r + k1 + sqrt (&3)= (r + k1) + sqrt (&3)`]);;

let bdt7_finiteness=prove(`!(x:real^3)(k1:real)(k2:real) (r:real). (&0< k1 /\ &0< k2 /\ r< k2 + sqrt (&3) /\ k2 <= r) ==> ?(C:real). &(CARD ((int_ball x (r+ k1)) DIFF (int_ball x (r- k2))))<= C* r pow 2`,
		  REPEAT STRIP_TAC THEN EXISTS_TAC `(&4/ &3*pi*(k2+k1+ &2*sqrt(&3)) pow 3/ (k2 pow 2)):real`
	    THEN MATCH_MP_TAC(REAL_ARITH `&(CARD (int_ball x (r + k1) DIFF int_ball x (r - k2)))
<= &4/ &3*pi*(r+k1+ sqrt(&3))pow 3 /\ &4/ &3*pi*(r+k1+ sqrt(&3))pow 3 <= (&4 / &3 * pi * (k2 + k1 + &2 * sqrt (&3)) pow 3 / k2 pow 2) * r pow 2 ==> &(CARD (int_ball x (r + k1) DIFF int_ball x (r - k2))) <= ( &4 / &3 * pi * (k2 + k1 + &2 * sqrt (&3)) pow 3 / k2 pow 2) * r pow 2`)		    THEN MP_TAC(REAL_ARITH `&0< k2 /\ k2<= r ==> &0< r`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
	    THEN ASM_SIMP_TAC[SPECL [`x:real^3`;`k1:real`;`k2:real`; `r:real`] bdt6_finiteness]
	    THEN MATCH_MP_TAC(REAL_ARITH `&4 / &3 * pi * (r + k1 + sqrt (&3)) pow 3 
<= &4 / &3 * pi * (k2 + k1 + &2*sqrt (&3)) pow 3 /\ &4 / &3 * pi * (k2 + k1 + &2*sqrt (&3)) pow 3 
<= (&4 / &3 * pi * (k2 + k1 + &2 * sqrt (&3)) pow 3 / k2 pow 2) * r pow 2 ==> &4 / &3 * pi * (r + k1 + sqrt (&3)) pow 3 <=
 (&4 / &3 * pi * (k2 + k1 + &2 * sqrt (&3)) pow 3 / k2 pow 2) * r pow 2`)
	    THEN MP_TAC(MESON[REAL_ARITH `&0<k1 /\ &0< r ==> sqrt(&3)<= r+k1+ sqrt(&3)`;SPEC `&3:real` SQRT_POS_LE;
REAL_ARITH `&0<= &3`;REAL_ARITH `a<=b /\ b<= c ==> a<= c`]  `&0<k1 /\ &0< r ==> &0<= r+k1+ sqrt(&3)`)
	    THEN ASM_REWRITE_TAC[] THEN MP_TAC(REAL_ARITH `r < k2 + sqrt (&3) ==> r+ k1+ sqrt(&3) <= k2+ k1+ &2* sqrt(&3)`) THEN ASM_REWRITE_TAC[] THEN MP_TAC(MESON[PI_POS_LE;REAL_ARITH `&0<= &4/ &3`;REAL_LE_MUL] `&0<= &4/ &3*pi`)
	    THEN REPEAT DISCH_TAC THEN MP_TAC(ISPECL [`3:num`;`r + k1 + sqrt (&3):real`;`k2 + k1 + &2 * sqrt (&3):real`] REAL_POW_LE2) THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_ARITH `(a:real)*b*c = (a*b)*c`;REAL_LE_LMUL]
    THEN DISCH_TAC THEN REWRITE_TAC[REAL_FIELD `((&4 / &3 * pi) * (k2 + k1 + &2 * sqrt (&3)) pow 3 / k2 pow 2) * r pow 2= ((&4 / &3 * pi)*((k2 + k1 + &2 * sqrt (&3)) pow 3))*(r pow 2/ k2 pow 2)`]
    THEN MP_TAC(MESON[MESON[REAL_POW_LE] `&0 <= r + k1 + sqrt (&3) ==> &0 <= (r + k1 + sqrt (&3)) pow 3`;REAL_ARITH `a<= b /\ b<= c ==> a<= c`] `&0 <= r + k1 + sqrt (&3) /\ (r + k1 + sqrt (&3)) pow 3 <= (k2 + k1 + &2 * sqrt (&3)) pow 3 ==> &0<= (k2 + k1 + &2 * sqrt (&3)) pow 3`) THEN ASM_REWRITE_TAC[]   THEN MP_TAC(SPECL [`r:real`;`k2:real`;`2:num`] bdt2_finiteness) THEN ASM_REWRITE_TAC[]
	  THEN REPEAT DISCH_TAC THEN MP_TAC(MESON[REAL_LE_MUL] `&0 <= &4 / &3 * pi /\ &0 <= (k2 + k1 + &2 * sqrt (&3)) pow 3 ==> &0<= (&4 / &3 * pi) * (k2 + k1 + &2 * sqrt (&3)) pow 3`) THEN ASM_REWRITE_TAC[] 
THEN ASM_MESON_TAC[REAL_LE_LMUL;REAL_ARITH ` a* &1= a`]);;

(*--------------------------------------------------------------------*)
(*Lemma 2.16 [TXIWYHI] Bound of number of int points between two balls*)
(*--------------------------------------------------------------------*)


let TXIWYHI=prove( `!(x:real^3)(k1:real)(k2:real) (r:real). 
    (&0< k1 /\ &0< k2 /\ k2 <= r) ==> ?(C:real).
     &(CARD (integer_point (ball(x,r+ k1) DIFF ball(x,r- k2))))<= C* r pow 2`, 
  REPEAT GEN_TAC THEN SIMP_TAC[eq_def_intball]
  THEN STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH `(r:real)< k2+ sqrt(&3) \/ (k2+ sqrt(&3)<= r)`)
  THENL [ASM_MESON_TAC[bdt7_finiteness];ASM_MESON_TAC[bdt5_finiteness]]);;


(*--------------------------------------------------------------------*)


