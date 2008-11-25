(*Nguyen Tat Thang*)


(*Definition of null set*)

needs "Multivariate/vectors.ml";;
needs "definitions_kepler.ml";;

(* tchales, topology.ml is incompatible with previously loaded files *)
(* needs "Multivariate/topology.ml";; *)


let sphere= new_definition`sphere x=(?(v:real^3)(r:real). (r> &0)/\ (x={w:real^3 | norm (w-v)= r}))`;;

(* It is enough to work with one branch of the cone.  This
simplifies the definition a bit *)
(*
let c_cone = new_definition `c_cone (v,w:real^3, r:real)={x:real^3 | (x=v) \/ ((x-v) dot w 
= norm (x-v)* norm w* r)\/ ((x-v) dot w = --norm (x-v)* norm w* r)}`;;
*)
let c_cone = new_definition `c_cone (v,w:real^3, r:real)={x:real^3 | ((x-v) dot w = norm (x-v)* norm w* r)}`;;

let circular_cone =new_definition `circular_cone (V:real^3-> bool)=
(? (v,w:real^3)(r:real). V= c_cone (v,w,r))`;;

let NULLSET_RULES,NULLSET_INDUCT,NULLSET_CASES =
  new_inductive_definition
    `(!P. ((plane P)\/ (sphere P) \/ (circular_cone P)) ==> NULLSET P) /\
     !(s:real^3->bool) t. (NULLSET s /\ NULLSET t) ==> NULLSET (s UNION t)`;;


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

g `!r s (x:real^3) C. radial r x C /\ (s > &0) /\ (s < r) ==> (C INTER normball x s = IMAGE ((+) x) (IMAGE (scale (s/r % (vec 1)))(IMAGE ((+) (--x)) (C INTER normball x r))))`;;

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

e (ASM_MESON_TAC[radial]);;

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

e (ASM_MESON_TAC[radial]);;

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



g `! (C:real^3->bool) (x:real^3) r s. measurable C /\ volume_props (vol) /\ radial r x C /\ (s > &0) /\ (s < r) ==> measurable (C INTER normball x s) /\ vol (C INTER normball x s)= vol (C) *(s/r) pow 3`;;

e (REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC);;

e (ASM_MESON_TAC[MEASURABLE_RULES;measurable_normball]);;

e (SUBGOAL_THEN `C INTER normball x s = IMAGE ((+) x) (IMAGE (scale (s/r % (vec 1)))(IMAGE ((+) (--x)) (C INTER normball x r)))` ASSUME_TAC);;

e (ASM_SIMP_TAC[trans_strech_trans_radial]);;

e (ASM_REWRITE_TAC[]);;

e (SUBGOAL_THEN `measurable (C INTER normball x r)` ASSUME_TAC);;

e (ASM_MESON_TAC[MEASURABLE_RULES;measurable_normball]);;

e (SUBGOAL_THEN `measurable (IMAGE ((+) (--x)) (C INTER normball x r))` ASSUME_TAC);;

e (ASM_MESON_TAC[MEASURABLE_RULES]);;

e (SUBGOAL_THEN `measurable (IMAGE (scale (s / r % vec 1)) (IMAGE ((+) (--x)) (C INTER normball x r)))` ASSUME_TAC);;

e (ASM_MESON_TAC[MEASURABLE_RULES]);;

e (SUBGOAL_THEN `measurable (IMAGE ((+) x)
 (IMAGE (scale (s / r % vec 1)) (IMAGE ((+) (--x)) (C INTER normball x r))))` ASSUME_TAC);;

e (ASM_MESON_TAC[MEASURABLE_RULES]);;

e (ABBREV_TAC `A2:real^3->bool= (IMAGE (scale (s / r % vec 1))
      (IMAGE ((+) (--x)) (C INTER normball x r)))`);;

e (SUBGOAL_THEN `vol (IMAGE ((+) x) A2)=vol (A2)` MP_TAC);;

e (UNDISCH_TAC `(volume_props vol):bool`);;

e (UNDISCH_TAC `(measurable A2):bool`);;

e (REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (SIMP_TAC[volume_props]);;

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

e (UNDISCH_TAC `(volume_props vol):bool`);;

e (UNDISCH_TAC `(measurable M1):bool`);;

e (REWRITE_TAC[TAUT `P1 ==> P2 ==> P3 ==> P4 <=> P1 /\ P2 /\ P3 ==> P4`]);;

e (SIMP_TAC[volume_props]);;

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

e (UNDISCH_TAC `(IMAGE ((+) (--x:real^3)) (C INTER normball x r) = M1):bool`);;

e (REWRITE_TAC[SET_RULE `IMAGE ((+) (--x)) (C INTER normball x r) = M1 <=> M1= IMAGE ((+) (--x)) (C INTER normball x r)`]);;

e (SIMP_TAC[]);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `vol (IMAGE ((+) (--x)) (C INTER normball x r))= vol (C INTER normball (x:real^3) r)` MP_TAC);;

e (UNDISCH_TAC `(volume_props vol):bool`);;

e (UNDISCH_TAC `(measurable (C INTER normball x r)):bool`);;

e (REWRITE_TAC[TAUT `A==>B==>C <=> A/\B==>C`]);;

e (SIMP_TAC[volume_props]);;

e (SIMP_TAC[]);;

e (DISCH_TAC);;

e (SUBGOAL_THEN `C INTER normball (x:real^3) r= C` MP_TAC);;

e (UNDISCH_TAC `(radial r (x:real^3) C):bool`);;

e (REWRITE_TAC[radial]);;

e (REPEAT STRIP_TAC);;

e (UNDISCH_TAC `(C SUBSET normball (x:real^3) r):bool`);;

e (SIMP_TAC[SUBSET_INTER_ABSORPTION]);;

e (DISCH_TAC);;

e (ABBREV_TAC `(E:real^3->bool)= C INTER normball x r`);;

e (ASM_MESON_TAC[]);;

e (ABBREV_TAC `a:real= (s / r) pow 3`);;

e (ABBREV_TAC `a1:real= vol M1` THEN ABBREV_TAC `a2:real= vol C`);;

e (SIMP_TAC[]);;

let lemma_r_r'=top_thm();; 








(*---------------------------------------------------------------------------------------------------------------*)



(*Lemma 4.3*)


let tr5=prove(`!r v0 C C'.(radial r v0 C /\ radial r v0 C' ==> (!u. ((v0+u) IN (C INTER C')) ==> (!t.(t > &0) /\ (t * norm u < r)==> (v0+t % u IN (C INTER C')))))`, REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTER] THEN MESON_TAC[radial;IN_INTER]);;
let tr6=prove(`!r v0 C C'.(radial r v0 C /\ radial r v0 C' ==> C INTER C' SUBSET normball v0 r)`, REPEAT GEN_TAC THEN MESON_TAC[radial;INTER_SUBSET;SUBSET_TRANS]);;

let inter_radial =prove(`!r v0 C C'.(radial r v0 C /\ radial r v0 C') ==> radial r v0 (C INTER C')`, REPEAT GEN_TAC THEN MESON_TAC[radial;tr5;tr6]);; 


(*4.2.11 combining solid angle and volume*)

(* removed by thales, nov 11, 2008.  Conflicts with definition of phi already provided *)

(*
let phi=new_definition `phi(h:real,t:real,l:real^2)= l$1*t*h*(t+h)/ &6 + l$2`;;
let A=new_definition `A(h:real,t:real,l:real^2)=(&1-h/t)*(phi (h,t,l)-phi (t,t,l))`;;

*)



