(*Nguyen Tat Thang*)


(*Definition of null set*)

needs "Multivariate/vector.ml";;
needs "definitions_kepler.ml";;
needs "Multivariate/topology.ml";;


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



(*Lemma 4.3*)


let tr5=prove(`!r v0 C C'.(radial r v0 C /\ radial r v0 C' ==> (!u. ((v0+u) IN (C INTER C')) ==> (!t.(t > &0) /\ (t * norm u < r)==> (v0+t % u IN (C INTER C')))))`, REPEAT GEN_TAC THEN REWRITE_TAC[IN_INTER] THEN MESON_TAC[radial;IN_INTER]);;
let tr6=prove(`!r v0 C C'.(radial r v0 C /\ radial r v0 C' ==> C INTER C' SUBSET normball v0 r)`, REPEAT GEN_TAC THEN MESON_TAC[radial;INTER_SUBSET;SUBSET_TRANS]);;

let inter_radial =prove(`!r v0 C C'.(radial r v0 C /\ radial r v0 C') ==> radial r v0 (C INTER C')`, REPEAT GEN_TAC THEN MESON_TAC[radial;tr5;tr6]);; 


(*4.2.11 combining solid angle and volume*)


let phi=new_definition `phi(h:real,t:real,l:real^2)= l$1*t*h*(t+h)/ &6 + l$2`;;
let A=new_definition `A(h:real,t:real,l:real^2)=(&1-h/t)*(phi (h,t,l)-phi (t,t,l))`;;



