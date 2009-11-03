
(* Hoang Le Truong *)

(* since you define C0,C1 independently, you need lemmas to relate this to other chapters.

lemmas 
`aff_gt {v} {v1,v2}={t1 % v+t2 % v1+t3 % v2 | ?t1 t2 t3. (t2 > &0)/\(t3 > &0)/\(t1+t2+t3= &1)}`;;

`aff_ge {v} {v1,v2}={t1 % v+t2 % v1+t3 % v2 | ?t1 t2 t3. (t2 >= &0)/\(t3 >= &0)/\(t1+t2+t3= &1)}`;;

*)

  needs "Multivariate/flyspeck.ml";;
needs "sphere.hl";;
needs "hypermap.hl";;


let graph = new_definition `graph E <=> (!e. E e ==> (e HAS_SIZE 2))`;;

let fan1 = new_definition`fan1(x,V,E):bool <=>  FINITE V /\ ~(V SUBSET {}) `;;

let fan2 = new_definition`fan2(x,V,E):bool <=>   ~(x IN V)`;;

let fan3=new_definition`fan3(x,V,E):bool <=> (!v. (v IN V) ==> cyclic_set {w | {v,w} IN E } x v)`;;

let fan4 = new_definition`fan4(x,V,E):bool<=>  (!e. (e IN E) ==> (aff_gt {x} e  INTER V={}))`;;

let fan5 = new_definition`fan5(x,V,E):bool<=> (!e f. (e IN E)/\ (f IN E) /\ ~(e=f) ==> (aff_gt {x} e INTER aff_gt {x} f ={}))`;;

let fan = new_definition`fan(x,V,E)<=>  ((UNIONS E) SUBSET V) /\ graph(E)/\ fan1(x,V,E)/\ fan2(x,V,E)/\ fan3(x,V,E)/\ fan4 (x,V,E) /\ fan5(x,V,E)`;;

let base_point_fan=new_definition`base_point_fan (x,V,E)=x`;;

let set_of_edges=new_definition`set_of_edges v E={w|{v,w} IN E}`;;

let set_of_edge=new_definition`set_of_edge v V E={w|{v,w} IN E /\ w IN V}`;;


let fan6= new_definition`fan6(x,V,E):bool<=>(!e. (e IN E) ==> ~(collinear ({x} UNION e)))`;;

let fan7= new_definition`fan7(x,V,E):bool<=> (!e1 e2. (e1 IN E UNION {{v}| v IN V}) /\ (e2 IN E UNION {{v}| v IN V})
==> ((aff_ge {x} e1) INTER (aff_ge {x} e2) = aff_ge {x} (e1 INTER e2)))`;;



let FAN=new_definition`FAN(x,V,E) <=> ((UNIONS E) SUBSET V) /\ graph(E) /\ fan1(x,V,E) /\ fan2(x,V,E)/\
fan6(x,V,E)/\ fan7(x,V,E)`;;








(* ************************************************* *)
(* Proof remark rem:fan *)


let remark_fan1=prove(`!v w V E. (v IN V) /\ (w IN V) ==>((w IN set_of_edge v V E)<=>(v IN set_of_edge w V E))`, 
(let lemma=prove(`{w,v}={v,w}`, SET_TAC[]) in
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[set_of_edge;IN_ELIM_THM]  THEN ASM_REWRITE_TAC[] THEN MESON_TAC[lemma]));;

let remark_finite_fan1=prove(
`!v:real^3 (V:real^3->bool) (E:(real^3->bool)->bool). FINITE V ==> FINITE (set_of_edge v V E)`,
REPEAT GEN_TAC THEN DISCH_TAC 
  THEN MP_TAC(ISPECL [`(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))`; `V:real^3->bool`] FINITE_SUBSET) 
  THEN ASM_REWRITE_TAC[]
  THEN REWRITE_TAC[set_of_edge] THEN SET_TAC[] );;



let properties_of_set_of_edge=prove(`!v:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) u:real^3.  UNIONS E SUBSET V
==>
({v,u} IN E <=> u IN set_of_edge v V E)`,
REPEAT GEN_TAC THEN REWRITE_TAC[UNIONS; SUBSET; set_of_edge ; IN_ELIM_THM] 
THEN STRIP_TAC
 THEN POP_ASSUM(fun th-> MP_TAC(ISPEC `u:real^3`th)) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN DISCH_TAC
  THEN POP_ASSUM(fun th-> MP_TAC(ISPEC `{(v:real^3),(u:real^3)}`th)) THEN SET_TAC[]);;
let properties_of_set_of_edge_fan=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3.  FAN(x,V,E)
==>
({v,u} IN E <=> u IN set_of_edge v V E)`,
REWRITE_TAC[FAN] THEN REPEAT GEN_TAC THEN REWRITE_TAC[UNIONS; SUBSET; set_of_edge ; IN_ELIM_THM] 
THEN STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC"a") THEN STRIP_TAC 
 THEN REMOVE_THEN "a"(fun th-> MP_TAC(ISPEC `u:real^3`th)) THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN DISCH_TAC
  THEN POP_ASSUM(fun th-> MP_TAC(ISPEC `{(v:real^3),(u:real^3)}`th)) THEN SET_TAC[]);;



let properties_of_graph=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (u:real^3) (v:real^3). 
FAN(x,V,E) /\{v,u} IN E==> v IN V`,

REPEAT GEN_TAC THEN REWRITE_TAC[FAN] THEN STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN DISCH_THEN(LABEL_TAC "a") THEN REPEAT STRIP_TAC THEN
REMOVE_THEN "a" MP_TAC THEN REWRITE_TAC[UNIONS; SUBSET; IN_ELIM_THM] THEN DISCH_TAC 
  THEN POP_ASSUM(fun th-> MP_TAC(ISPEC`v:real^3` th)) THEN DISCH_TAC
THEN POP_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `{(v:real^3),(u:real^3)}` THEN SET_TAC[]);;

 



let th3a=prove(`!x v u.(~ collinear {x,v,u} ==> DISJOINT {x,v} {u})`,
   (let th=prove(`{x,v,u}={x,u,v}`, SET_TAC[]) in
REPEAT GEN_TAC THEN REWRITE_TAC[th;IN_DISJOINT] THEN MATCH_MP_TAC MONO_NOT THEN 
REWRITE_TAC[COLLINEAR_3;COLLINEAR_LEMMA; VECTOR_ARITH` a-b= vec 0 <=> a = b`; IN_SING] THEN STRIP_TAC 
  THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN(LABEL_TAC "a") THEN DISCH_TAC THEN REMOVE_THEN "a" MP_TAC 
THEN ASM_REWRITE_TAC[] THEN SET_TAC[]));; 
   let th3b=prove(`!x v u. ~ collinear {x,v,u} ==> ~(x=v) `,
REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_3;COLLINEAR_LEMMA; VECTOR_ARITH` a-b= vec 0 <=> a = b`; DE_MORGAN_THM] THEN SET_TAC[]);; 
let th3b1=prove(`!x v u. ~ collinear {x,v,u} ==> ~(x=u) `,
(let th=prove(`{x,v,u}={x,u,v}`, SET_TAC[]) in
REWRITE_TAC[th;th3b]));; 

   let th3c= prove(`!x v u. ~ collinear {x,v,u} ==> ~(u IN aff {x,v})`,
REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_NOT 
THEN REWRITE_TAC[aff; AFFINE_HULL_2; IN_ELIM_THM;COLLINEAR_3;COLLINEAR_LEMMA; VECTOR_ARITH` a-b= vec 0 <=> a = b`; DE_MORGAN_THM] 
THEN STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[REAL_ARITH `u'+v'= &1 <=> v'= &1 -u'`] 
  THEN DISCH_TAC THEN ASM_REWRITE_TAC[] 
THEN REWRITE_TAC[VECTOR_ARITH`(u = u' % x + (&1 - u') % v) <=> (u - v = u' % (x-v))`] THEN SET_TAC[]);;
   

let th3d=prove(`!x v u. ~(x=v)/\ ~(x=u) ==> DISJOINT {x} {v,u}`,
SET_TAC[]);;

let th3=prove(`!x v u. ~ collinear {x,v,u} ==> ~ (x=v) /\ ~(x=u) /\ DISJOINT {x,v} {u}/\ ~(u IN aff {x,v})/\DISJOINT {x} {v,u}`, 
MESON_TAC[th3a;th3b;th3b1;th3c;th3d]);;


let collinear1_fan=prove(`!x v u. ~ collinear {x,u,v} <=> ~(u IN aff {x,v})/\ ~ (x=v)`,
(let lem=prove(`!x v u. {x,v,u}= {x,u,v}`,SET_TAC[]) in
REPEAT GEN_TAC THEN EQ_TAC
THENL[
MESON_TAC[th3;lem];
REWRITE_TAC[SET_RULE`~(t1) /\ ~ t2<=> ~(t2\/ t1)`;COLLINEAR_3_EXPAND;aff; AFFINE_HULL_2;IN_ELIM_THM] 
THEN MATCH_MP_TAC MONO_NOT  THEN MATCH_MP_TAC MONO_OR THEN STRIP_TAC 
THENL[
REWRITE_TAC[];

STRIP_TAC THEN EXISTS_TAC`u':real` THEN EXISTS_TAC`&1- (u':real)` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]));;


let collinear_fan=prove(`!x v u. ~ collinear {x,v,u} <=> ~(u IN aff {x,v})/\ ~ (x=v)`,
(let lem=prove(`!x v u. {x,v,u}= {x,u,v}`,SET_TAC[]) in
MESON_TAC[collinear1_fan;lem]));;


let th4=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (u:real^3) (v:real^3). 
FAN(x,V,E) /\{v,u} IN E==> ~(x=v)`,
REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (u:real^3)`; `(v:real^3)`]properties_of_graph) THEN ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[FAN;fan2] THEN SET_TAC[]);;


let collinears_fan=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (u:real^3) (v:real^3). 
FAN(x,V,E) /\{v,u} IN E==>( ~ collinear {x,v,u} <=> ~(u IN aff {x,v}))`,
MESON_TAC[th4;collinear_fan]);;




(*let azim_cycle_fan= new_definition`azim_cycle_fan   = 
(  !x:real^3 V E. ?sigma. !proj e1 e2 e3 v w. 
(fan(x, V, E) /\ (V v) /\ ({v,w} IN E) /\ ((dist(v,x)) % e3 = (x-v)) /\
(orthonormal e1 e2 e3) /\
(!u a b. (proj u = (a,b)) <=> (?h. (u = v + a % e1 + b % e2 + h % e3)))) 
==> (  (proj (sigma  v w) = polar_cycle (IMAGE proj {y|{v,y} IN E}) (proj w)))) `;;

let azim_cycle_fan1 = REWRITE_RULE[SKOLEM_THM] azim_cycle_fan;;

let azim_cycle_fan2=prove(`?sigma. !x:real^3 V E proj e1 e2 e3 v w. 
(azim_cycle_fan)==>
(fan(x, V, E) /\ (V v) /\ ({v,w} IN E) /\ ((dist(v,x)) % e3 = (x-v)) /\
(orthonormal e1 e2 e3) /\
(!u a b. (proj u = (a,b)) <=> (?h. (u = v + a % e1 + b % e2 + h % e3)))) 
==> (  (proj (sigma x V E v w) = polar_cycle (IMAGE proj {y|{v,y} IN E}) (proj w))) `,
REWRITE_TAC[GSYM RIGHT_IMP_FORALL_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN 
REWRITE_TAC[azim_cycle_fan1]);;
	





let sigma_fan= new_specification ["sigma_fan"] azim_cycle_fan2;;*)


let sigma_fan=new_definition`sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)=  
(if (set_of_edge v V E= {u} ) then u 
    else (@(w:real^3).  (w IN (set_of_edge v V E)) /\ ~(w=u) /\
(!(w1:real^3). (w1 IN (set_of_edge v V E))/\ ~(w1=u) ==> azim x v u w <= azim x v u w1)))`;;

let extension_sigma_fan=new_definition`extension_sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)=  
(if ~(u IN set_of_edge v V E ) then u 
    else (sigma_fan x V E v u))`;;





let exists_sigma_fan=prove(`
(!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3).
~ (set_of_edge v V E= {u} ) 
/\ FAN(x,V,E) /\ (u IN (set_of_edge v V E))
==>
(?(w:real^3). (w IN (set_of_edge v V E)) /\ ~(w=u) /\
(!(w1:real^3). (w1 IN (set_of_edge v V E))/\ ~(w1=u) ==> azim x v u w <= azim x v u w1)))
`,

(let lemma = prove
   (`!X:real->bool. 
          FINITE X /\ ~(X = {}) 
          ==> ?a. a IN X /\ !x. x IN X ==> a <= x`,
    MESON_TAC[INF_FINITE]) in


MP_TAC(lemma) THEN DISCH_THEN(LABEL_TAC "a") THEN REPEAT GEN_TAC THEN REWRITE_TAC[FAN;fan1] THEN STRIP_TAC THEN MP_TAC (ISPECL[`(v:real^3)` ;`(V:real^3->bool)`; `(E:(real^3->bool)->bool)`]remark_finite_fan1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  
SUBGOAL_THEN `FINITE ((set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) DELETE  (u:real^3))` ASSUME_TAC
THENL[(*2*)
ASM_MESON_TAC[FINITE_DELETE_IMP];(*2*)

DISJ_CASES_TAC(SET_RULE`((set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) DELETE  (u:real^3)={})\/
 ~((set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) DELETE  (u:real^3)={})`)
THENL[(*3*)
POP_ASSUM MP_TAC THEN REWRITE_TAC[DELETE;EXTENSION;IN_ELIM_THM] THEN DISCH_TAC
  THEN SUBGOAL_THEN `set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={u:real^3}` ASSUME_TAC
THENL[(*4*)
SET_TAC[];(*4*)
SET_TAC[]](*4*);(*3*)
SUBGOAL_THEN`~(IMAGE (azim x v u) ((set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) DELETE  (u:real^3))={})` ASSUME_TAC
THENL[(*4*)
REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM_MESON_TAC[];(*4*)

SUBGOAL_THEN` FINITE (IMAGE (azim x v u) ((set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) DELETE  (u:real^3)))` ASSUME_TAC
THENL[(*5*)
ASM_MESON_TAC[FINITE_IMAGE];(*5*)
REMOVE_THEN "a" (fun th ->MP_TAC(ISPEC `(IMAGE (azim x v u) ((set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) DELETE  (u:real^3)))` th)) 
  THEN ASM_REWRITE_TAC[IMAGE;DELETE;IN_ELIM_THM] THEN STRIP_TAC THEN EXISTS_TAC`x':real^3`
  THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]
](*5*)](*4*)](*3*)](*2*)(*1*)));;


let azim1=new_definition`azim1 (x:real^3) (v:real^3) (u:real^3) (w:real^3)= &2 * pi- azim x v u w`;;


let exists_inverse_sigma_fan=prove(`
(!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3).
~ (set_of_edge v V E= {u} ) 
/\ FAN(x,V,E) /\ (u IN (set_of_edge v V E))
==>
(?(w:real^3). (w IN (set_of_edge v V E)) /\ ~(w=u) /\
(!(w1:real^3). (w1 IN (set_of_edge v V E))/\ ~(w1=u) ==> azim1 x v u w <=  azim1 x v u w1)))
`,
(let lemma = prove
   (`!X:real->bool. 
          FINITE X /\ ~(X = {}) 
          ==> ?a. a IN X /\ !x. x IN X ==> a <= x`,
    MESON_TAC[INF_FINITE]) in
MP_TAC(lemma) THEN DISCH_THEN(LABEL_TAC "a") THEN REPEAT GEN_TAC THEN REWRITE_TAC[FAN;fan1] THEN STRIP_TAC THEN MP_TAC (ISPECL[`(v:real^3)` ;`(V:real^3->bool)`; `(E:(real^3->bool)->bool)`]remark_finite_fan1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
SUBGOAL_THEN `FINITE ((set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) DELETE  (u:real^3))` ASSUME_TAC
THENL[(*2*)

ASM_MESON_TAC[FINITE_DELETE_IMP];(*2*)
DISJ_CASES_TAC(SET_RULE`((set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) DELETE  (u:real^3)={})\/
 ~((set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) DELETE  (u:real^3)={})`)
THENL[(*3*)
POP_ASSUM MP_TAC THEN REWRITE_TAC[DELETE;EXTENSION;IN_ELIM_THM] THEN DISCH_TAC
  THEN SUBGOAL_THEN `set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={u:real^3}` ASSUME_TAC
THENL[(*4*)
SET_TAC[];(*4*)
SET_TAC[](*4*)];

SUBGOAL_THEN`~(IMAGE ( azim1 x v u) ((set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) DELETE  (u:real^3))={})` ASSUME_TAC
THENL[(*4*)
REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM_MESON_TAC[];(*4*)
SUBGOAL_THEN` FINITE (IMAGE (azim1 x v u) ((set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) DELETE  (u:real^3)))` ASSUME_TAC
THENL[(*5*)
ASM_MESON_TAC[FINITE_IMAGE];(*5*)
REMOVE_THEN "a" (fun th ->MP_TAC(ISPEC `(IMAGE (azim1 x v u) ((set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) DELETE  (u:real^3)))` th)) 
  THEN ASM_REWRITE_TAC[IMAGE;DELETE;IN_ELIM_THM]THEN STRIP_TAC
THEN EXISTS_TAC`x':real^3`
  THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]
](*5*)](*4*)](*3*)](*2*)(*1*)));;








let SIGMA_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3).
~ (set_of_edge v V E= {u} ) 
/\ FAN(x,V,E) /\ (u IN (set_of_edge v V E))
==>
((sigma_fan x V E v u) IN (set_of_edge v V E)) /\ ~((sigma_fan x V E v u)=u) /\
(!(w1:real^3). (w1 IN (set_of_edge v V E))/\ ~(w1=u) ==> azim x v u (sigma_fan x V E v u) <= azim x v u w1)`,

REPEAT GEN_TAC THEN STRIP_TAC THEN ONCE_REWRITE_TAC[sigma_fan]
  THEN MP_TAC(ISPECL[`(x:real^3)`; `(V:real^3->bool)`; `(E:(real^3->bool)->bool)`; `(v:real^3)`; `(u:real^3)`]exists_sigma_fan)  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN SELECT_ELIM_TAC THEN EXISTS_TAC`w:real^3` THEN ASM_REWRITE_TAC[]);;

let AFF_GE_2_1 = prove
 (`!x v w.
        DISJOINT {x,v} {w}
        ==> aff_ge {x,v} {w} =
             {y | ?t1 t2 t3.
                     &0 <= t3 /\
                     t1 + t2 + t3 = &1 /\
                     y = t1 % x + t2 % v + t3 % w}`,
  AFF_TAC);;

let AFF_GE_1_2 = prove
 (`!x v w.
        DISJOINT {x} {v,w}
        ==> aff_ge {x} {v,w} =
             {y | ?t1 t2 t3.
                     &0 <= t2 /\ &0 <= t3 /\
                     t1 + t2 + t3 = &1 /\
                     y = t1 % x + t2 % v + t3 % w}`,
  AFF_TAC);;
let AFF_GE_1_1 = prove
 (`!x v w.
        DISJOINT {x} {v}
        ==> aff_ge {x} {v} =
             {y | ?t1 t2.
                     &0 <= t2 /\
                     t1 + t2 = &1 /\
                     y = t1 % x + t2 % v }`,
  AFF_TAC);;




let UNIQUE_FOINT_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) w:real^3.
FAN(x,V,E) /\ ({v,u} IN E) /\ ({v,w} IN E)/\
 ~(aff_ge {x} {v,u} INTER aff_ge {x} {v,w}=aff_ge {x} {v}) 
==> u=w`,
REPEAT GEN_TAC THEN REWRITE_TAC[FAN;fan7;fan6] THEN STRIP_TAC 
  THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC
  THEN DISCH_THEN (LABEL_TAC "a") THEN REPEAT STRIP_TAC
  THEN REMOVE_THEN "a" (fun th-> MP_TAC(ISPECL[`{(v:real^3),(u:real^3)}`;`{(v:real^3),(w:real^3)}`]th)) 
  THEN ASM_REWRITE_TAC[UNION;IN_ELIM_THM;]
  THEN DISJ_CASES_TAC(SET_RULE`~((u:real^3)=(w:real^3))\/ ((u:real^3)=(w:real^3))`)
THENL
[  MP_TAC(SET_RULE`~((u:real^3)=(w:real^3))==> {(v:real^3),(u:real^3)} INTER {(v:real^3),(w:real^3)}={v}`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
SET_TAC[]]);;

 







let UNIQUE1_POINT_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) w:real^3.
FAN(x,V,E) /\ ({v,u} IN E) /\ ({v,w} IN E)/\ w IN aff_gt {x,v} {u} 
==> u=w`,
REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC UNIQUE_FOINT_FAN THEN 
EXISTS_TAC `x:real^3` THEN EXISTS_TAC `V:real^3->bool` THEN EXISTS_TAC `E:(real^3->bool)->bool` THEN EXISTS_TAC `v:real^3`
	   THEN ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC)
	   THEN REWRITE_TAC[FAN;fan1;fan2;fan6;fan7] THEN REPEAT STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC)
	   THEN DISCH_TAC THEN  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC
	   THEN DISCH_THEN (LABEL_TAC "a")
	   THEN DISCH_THEN (LABEL_TAC "b") THEN REPEAT DISCH_TAC THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[]
THEN REMOVE_THEN "a" (fun th-> MP_TAC(ISPEC `{(v:real^3),(w:real^3)}`th) THEN ASSUME_TAC(th)) 
  THEN POP_ASSUM (fun th-> MP_TAC(ISPEC `{(v:real^3),(u:real^3)}`th))
  THEN ASM_REWRITE_TAC[SET_RULE`{a} UNION {b,c}={a,b,c}`]
	   THEN POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC "c")
	   THEN DISCH_TAC THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (w:real^3)`]th3) THEN ASM_REWRITE_TAC[]
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (u:real^3)`]th3) THEN ASM_REWRITE_TAC[]
	   THEN DISCH_TAC THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (u:real^3)`]AFF_GT_2_1) THEN ASM_REWRITE_TAC[]
	   THEN DISCH_TAC THEN REMOVE_THEN "c" MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC
	   THEN SUBGOAL_THEN` aff_ge {(x:real^3)} {(v:real^3)} SUBSET aff {x,v}` ASSUME_TAC
THENL (*1*)[
MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (u:real^3)`]AFF_GE_1_1) 
THEN MP_TAC(SET_RULE`~((x:real^3) = (v:real^3))==> DISJOINT {x} {v}`)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC THEN ASM_REWRITE_TAC[aff;AFFINE_HULL_2] THEN SET_TAC[];(*1*)
	   
SUBGOAL_THEN `~((w:real^3) IN aff_ge {x} {v})` ASSUME_TAC 
THENL (*2*)[
SET_TAC[];(*2*)

POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "d") THEN DISJ_CASES_TAC(REAL_ARITH `(&0 <= (t2:real))\/ (&0 <= (-- (t2:real)))`)
THENL (*3*)[
 SUBGOAL_THEN `(w:real^3) IN aff_ge {(x:real^3)} {(v:real^3),(u:real^3)}` ASSUME_TAC
THENL (*4*)[
 MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (u:real^3)`]AFF_GE_1_2) 
   THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]
THEN EXISTS_TAC `t1:real` 
  THEN EXISTS_TAC `t2:real` THEN EXISTS_TAC `t3:real` THEN ASM_REWRITE_TAC[]
    THEN REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;(*4*)

 SUBGOAL_THEN `(w:real^3) IN aff_ge {(x:real^3)} {(v:real^3),(w:real^3)}` ASSUME_TAC
THENL (*5*)[
 MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (w:real^3)`]AFF_GE_1_2) 
   THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]
THEN EXISTS_TAC `&0:real` 
  THEN EXISTS_TAC `&0:real` THEN EXISTS_TAC `&1:real`  THEN REWRITE_TAC[VECTOR_ARITH`w= &0 % x+ &0 % v + &1 % w `] THEN REAL_ARITH_TAC;(*5*)

SET_TAC[]](*5*)](*4*);(*3*)

 SUBGOAL_THEN `(u:real^3) IN aff_ge {(x:real^3)} {(v:real^3),(w:real^3)}` ASSUME_TAC
THENL (*4*)[
 MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (w:real^3)`]AFF_GE_1_2) 
   THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]
THEN EXISTS_TAC `inv(t3:real) *(--(t1:real))` 
  THEN EXISTS_TAC `inv(t3:real)*(--(t2:real))` THEN EXISTS_TAC `inv(t3:real)` 
THEN MP_TAC(ISPEC `t3:real` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC(REAL_ARITH`&0< inv(t3:real)==> (&0 <= inv(t3:real))`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC(ISPECL [`inv (t3:real)`;`(--(t2:real))`] REAL_LE_MUL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN ASM_REWRITE_TAC[REAL_ARITH`inv(t3:real) * -- (t1:real)+ inv(t3) * --(t2:real) +inv (t3)=inv (t3)*(&1-t1-t2)`] THEN
MP_TAC(REAL_ARITH`(t1:real)+(t2:real)+(t3:real)= &1 ==> &1 - t1- t2=t3`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
MP_TAC(REAL_ARITH`&0<(t3:real)==> ~(t3= &0)`) THEN ASM_REWRITE_TAC[VECTOR_ARITH`
 (inv t3 * --t1) % x +
 (inv t3 * --t2) % v +
 inv t3 % (t1 % x + t2 % v + t3 % u)= (inv t3 * t3) % u `
] THEN DISCH_TAC
THEN MP_TAC(ISPEC `t3:real` REAL_MUL_LINV) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[VECTOR_ARITH ` v= &1 % v`];(*4*)

 SUBGOAL_THEN `(u:real^3) IN aff_ge {(x:real^3)} {(v:real^3),(u:real^3)}` ASSUME_TAC
THENL (*5*)[
 MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (u:real^3)`]AFF_GE_1_2) 
   THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]
THEN EXISTS_TAC `&0:real` 
  THEN EXISTS_TAC `&0:real` THEN EXISTS_TAC `&1:real`  THEN REWRITE_TAC[VECTOR_ARITH`u= &0 % x+ &0 % v + &1 % u `] THEN REAL_ARITH_TAC;(*5*)
SET_TAC[]](*5*)](*4*)](*3*)](*2*)](*1*));;


let UNIQUE_AZIM_POINT_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) w:real^3 w1:real^3.
FAN(x,V,E) /\ ({v,u} IN E) /\ ({v,w} IN E) /\ { v, w1} IN E /\ (azim x v u w =azim x v u w1) 
==> w=w1`,

REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN DISCH_TAC THEN POP_ASSUM(fun th-> MP_TAC(th) THEN ASSUME_TAC(th)) THEN REWRITE_TAC[FAN;fan6] THEN REPEAT STRIP_TAC THEN  REPEAT (POP_ASSUM MP_TAC) THEN DISCH_TAC
  THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN (LABEL_TAC "a") THEN REPEAT DISCH_TAC
  THEN REMOVE_THEN "a"(fun th ->MP_TAC(ISPEC`{(v:real^3),(u:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM(fun th ->MP_TAC(ISPEC `{(v:real^3),(w:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM(fun th ->MP_TAC(ISPEC `{(v:real^3),(w1:real^3)}`th)) THEN ASM_REWRITE_TAC[SET_RULE`{a} UNION {b,c}={a,b,c}`]
  THEN REPEAT STRIP_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;`(v:real^3) `;`(u:real^3) `;`w:real^3`;` w1:real^3`] AZIM_EQ) THEN 
ASM_REWRITE_TAC[] THEN DISCH_TAC THEN 
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (w:real^3)`;` w1:real^3`]UNIQUE1_POINT_FAN) THEN ASM_REWRITE_TAC[]
			       );;


let UNIQUE_AZIM_0_POINT_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) w:real^3.
FAN(x,V,E) /\ ({v,u} IN E) /\ ({v,w} IN E) /\ (azim x v u w = &0) 
==> u=w`,

REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN DISCH_TAC THEN POP_ASSUM(fun th-> MP_TAC(th) THEN ASSUME_TAC(th)) THEN REWRITE_TAC[FAN;fan6] THEN REPEAT STRIP_TAC THEN  REPEAT (POP_ASSUM MP_TAC) THEN DISCH_TAC
  THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN (LABEL_TAC "a") THEN REPEAT DISCH_TAC
  THEN REMOVE_THEN "a"(fun th ->MP_TAC(ISPEC`{(v:real^3),(u:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM(fun th ->MP_TAC(ISPEC `{(v:real^3),(w:real^3)}`th)) THEN ASM_REWRITE_TAC[SET_RULE`{a} UNION {b,c}={a,b,c}`]
  THEN REPEAT STRIP_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;`(v:real^3) `;`(u:real^3) `;`w:real^3`] AZIM_EQ_0_ALT) THEN 
ASM_REWRITE_TAC[] THEN DISCH_TAC THEN 
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`;` w:real^3`]UNIQUE1_POINT_FAN) THEN ASM_REWRITE_TAC[]
			       );;




let CYCLIC_SET_EDGE_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3).
FAN(x,V,E) /\ v IN V 
==> cyclic_set (set_of_edge v V E) x v`,
REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN DISCH_TAC THEN POP_ASSUM(fun th-> MP_TAC(th) THEN ASSUME_TAC(th)) THEN REWRITE_TAC[FAN; cyclic_set;fan1;fan2;fan6;fan7] THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC
  THENL(*1*)[SET_TAC[];(*1*)
STRIP_TAC
  THENL (*2*)[SET_TAC[remark_finite_fan1];(*2*)
 STRIP_TAC THENL(*3*)[

ASM_REWRITE_TAC[set_of_edge;IN_ELIM_THM] THEN
REPEAT GEN_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  DISCH_THEN(LABEL_TAC "a") THEN   DISCH_THEN(LABEL_TAC "b")
THEN STRIP_TAC THEN STRIP_TAC THEN
REMOVE_THEN "a" (fun th-> MP_TAC(ISPEC `{(v:real^3), (p:real^3)}` th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM (fun th-> MP_TAC(ISPEC `{(v:real^3), (q:real^3)}` th))
  THEN ASM_REWRITE_TAC[SET_RULE`{a} UNION {b,c}={a,b,c}`] THEN REPEAT STRIP_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (p:real^3)`]th3) THEN ASM_REWRITE_TAC[]
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (q:real^3)`]th3) THEN ASM_REWRITE_TAC[]
  THEN POP_ASSUM (fun th-> REWRITE_TAC[])
  THEN POP_ASSUM (fun th-> REWRITE_TAC[])
  THEN POP_ASSUM (fun th-> REWRITE_TAC[SYM(th)] THEN ASSUME_TAC(th))
  THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN `(q:real^3) IN aff_gt {(x:real^3),(v:real^3)} {(p:real^3)}` ASSUME_TAC

THENL (*4*)[
 MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (p:real^3)`]AFF_GT_2_1) THEN ASM_REWRITE_TAC[]
	   THEN DISCH_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]
   THEN EXISTS_TAC `--(h:real)` THEN EXISTS_TAC `(h:real)` THEN EXISTS_TAC `&1` THEN REWRITE_TAC[VECTOR_ARITH`q= (-- (h:real)) % x + (h:real) % v + &1 % (q+ h% (x-v))`] THEN REAL_ARITH_TAC;(*4*)

ASM_MESON_TAC[UNIQUE1_POINT_FAN]](*4*);(*3*)

REWRITE_TAC[INTER;EXTENSION;IN_ELIM_THM] THEN GEN_TAC 
THEN SUBGOAL_THEN`(x':real^3) IN set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) ==> ~(x' IN aff {x,v})`
ASSUME_TAC
THENL(*4*)[
ASM_REWRITE_TAC[set_of_edge;IN_ELIM_THM] THEN
REPEAT GEN_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  DISCH_THEN(LABEL_TAC "a") THEN   DISCH_THEN(LABEL_TAC "b")
THEN STRIP_TAC THEN STRIP_TAC THEN
REMOVE_THEN "a" (fun th-> MP_TAC(ISPEC `{(v:real^3), (x':real^3)}` th) )
  THEN ASM_REWRITE_TAC[SET_RULE`{a} UNION {b,c}={a,b,c}`] THEN STRIP_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (x':real^3)`]th3) THEN ASM_MESON_TAC[]; (*4*)

EQ_TAC THENL(*5*)[

POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "a") THEN STRIP_TAC THEN REMOVE_THEN "a" MP_TAC THEN ASM_REWRITE_TAC[aff];(*5*)

SET_TAC[]](*5*)](*4*)] (*3*)]]);;
 
let subset_cyclic_set_fan=prove(`!x:real^3 v:real^3 V:real^3->bool W:real^3->bool.
V SUBSET W /\ cyclic_set W x v ==> cyclic_set V x v`,

REPEAT GEN_TAC THEN REWRITE_TAC[cyclic_set] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] 
  THEN MP_TAC(ISPECL[`V:real^3->bool`;`W:real^3->bool`]FINITE_SUBSET) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;




let UNIQUE_SIGMA_FAN=prove(`
(!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (w:real^3).
~ (set_of_edge v V E= {u} ) 
/\ FAN(x,V,E) /\ (u IN (set_of_edge v V E))
/\ (w IN (set_of_edge v V E)) /\ ~(w=u) /\
(!(w1:real^3). (w1 IN (set_of_edge v V E))/\ ~(w1=u) ==> azim x v u w <= azim x v u w1)
==> sigma_fan x V E v u=w)`,

	(		   let th=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) w:real^3.
FAN(x,V,E) /\ ({v,u} IN E) /\ ({v,w} IN E)
==> (w IN aff_gt {x,v} {u} ==> u=w)`, MESON_TAC[UNIQUE1_POINT_FAN]
) in

ASSUME_TAC(th) THEN
REPEAT GEN_TAC  THEN STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC"123") THEN 
DISCH_TAC  THEN DISCH_THEN(LABEL_TAC "1") 
  THEN DISCH_THEN(LABEL_TAC "2") THEN DISCH_THEN(LABEL_TAC "3") THEN DISCH_THEN(LABEL_TAC "4") 
  THEN DISCH_THEN(LABEL_TAC"a") 
  THEN MP_TAC(ISPECL[`(x:real^3)`; `(V:real^3->bool)`; `(E:(real^3->bool)->bool)` ;`(v:real^3)`; `(u:real^3)`]SIGMA_FAN) 
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
  THEN REMOVE_THEN "a" (fun th->MP_TAC(ISPEC `sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)` th)) 
  THEN ASM_REWRITE_TAC[]
  THEN POP_ASSUM (fun th-> MP_TAC(ISPEC `w:real^3` th)) THEN ASM_REWRITE_TAC[] 
  THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC"b")
  THEN REPEAT DISCH_TAC
  THEN SUBGOAL_THEN `azim x v u (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)) = azim x v u (w:real^3)` ASSUME_TAC
THENL[
REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
REMOVE_THEN "123" (fun th->MP_TAC (ISPECL[`(x:real^3)`; `(V:real^3->bool)` ;`(E:(real^3->bool)->bool)`; `(v:real^3)` ; `(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3))`;`(w:real^3)`]th)) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
REMOVE_THEN"1" MP_TAC 
THEN  REWRITE_TAC[FAN;fan6;fan7] THEN STRIP_TAC THEN
POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC "c") THEN DISCH_THEN (LABEL_TAC "d")
  THEN REMOVE_THEN"2" MP_TAC THEN REMOVE_THEN"3" MP_TAC THEN REMOVE_THEN"b" MP_TAC 
  THEN REWRITE_TAC[set_of_edge;IN_ELIM_THM] THEN REPEAT STRIP_TAC
  THEN REMOVE_THEN "c" MP_TAC THEN DISCH_TAC
  THEN POP_ASSUM (fun th->MP_TAC (ISPEC`{(v:real^3),(w:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM (fun th->MP_TAC (ISPEC`{(v:real^3),(u:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM (fun th->MP_TAC (ISPEC`{(v:real^3),(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3))}`th) THEN ASSUME_TAC(th))
  THEN REWRITE_TAC[SET_RULE`{a} UNION {b,c}={a,b,c}`] THEN REPEAT STRIP_TAC  
  THEN MP_TAC(ISPECL[`(x:real^3)`; `(v:real^3)`; `(u:real^3)` ;`(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3))`; `(w:real^3)`]AZIM_EQ )
  THEN ASM_REWRITE_TAC[]
  THEN ASM_MESON_TAC[]]));; 








let d1_fan =new_definition`
d1_fan (x,V,E) ={(x:real^3,v:real^3,w:real^3,w1:real^3)|(V v)/\(w IN set_of_edge v V E)/\(w1 = sigma_fan x V E v w)}`;;




let d2_fan=new_definition`d2_fan (x,V,E)={ (x,v)| (V v) /\ ((set_of_edge v V E) ={})}`;;


let inverse_sigma_fan=new_definition`inverse_sigma_fan x V E v w = @a. sigma_fan x V E v a=w`;;

let e_fan=new_definition` e_fan (x:real^3) V E = (\((x:real^3),(v:real^3),(w:real^3),(w1:real^3)). (x,w,v,(sigma_fan x V E w v)))`;;


let f_fan=new_definition`f_fan (x:real^3) V E = (\((x:real^3),(v:real^3),(w:real^3),(w1:real^3)). (x,w,(inverse_sigma_fan x V E w v),v) )`;;

let n_fan=new_definition`n_fan (x:real^3) V E =(\((x:real^3),(v:real^3),(w:real^3),(w1:real^3)). (x,v,(sigma_fan x V E v w),(sigma_fan x V E v (sigma_fan x V E v w))))`;;

let i_fan=new_definition`i_fan (x:real^3) V E=(\((x:real^3),(v:real^3),(w:real^3),(w1:real^3)). (x,v,w,(sigma_fan x V E v w)))`;;

let pr1=new_definition`pr1=(\((x:real^3),(v:real^3),(w:real^3),(w1:real^3)). x)`;;

let pr2=new_definition`pr2=(\((x:real^3),(v:real^3),(w:real^3),(w1:real^3)). v)`;;

let pr3=new_definition`pr3=(\((x:real^3),(v:real^3),(w:real^3),(w1:real^3)). w)`;;

let pr4=new_definition`pr4=(\((x:real^3),(v:real^3),(w:real^3),(w1:real^3)). w1)`;;

let o_funs=new_definition`!(f:real^3#real^3#real^3#real^3->real^3#real^3#real^3#real^3) (g:real^3#real^3#real^3#real^3->real^3#real^3#real^3#real^3). o_funs f g =(\(x:real^3,y:real^3,z:real^3,t:real^3).  f (pr1 (g(x,y,z,t)),pr2(g(x,y,z,t)),pr3(g(x,y,z,t)),pr4(g(x,y,z,t))))`;;


let power_maps= new_recursive_definition num_RECURSION `(power_maps  (f:real^3->(real^3->bool)->((real^3->bool)->bool)->real^3#real^3#real^3#real^3->real^3#real^3#real^3#real^3) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) 0 = i_fan (x:real^3) V E) /\ (power_maps f x V E (SUC n)= o_funs (f x V E)  (power_maps f x V E n))`;;

let power_map_points= new_recursive_definition num_RECURSION `(power_map_points f x V E v w 0 = w)/\(power_map_points f x V E v w  (SUC n)= f x V E v (power_map_points f x V E v w n))`;;


 
let power_n_fan= new_definition`power_n_fan x V E n=( \(x,v,w,w1). (x,v,(power_map_points sigma_fan x V E v w n),(power_map_points sigma_fan x V E v w (SUC n))))`;; 


let a_node_fan=new_definition`a_node_fan x V E (x,v,w,w1)={a | ?n. a=(power_maps  n_fan x V E n) (x,v,w,sigma_fan x V E v w)}`;;









let xfan= new_definition`xfan (x,V,E)={v | ?e. (E e)/\(v IN aff_ge {x} e)}`;;

let yfan= new_definition`yfan (x,V,E)={v:real^3 | ?e. (E e)/\(~(v IN aff_ge {x} e))}`;;


let w_dart_fan=new_definition`w_dart_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) ((y:real^3),(v:real^3),(w:real^3),(w1:real^3))=  
if (CARD (set_of_edge v V E) > 1) then wedge x v w (sigma_fan x V E v w)
else  
(if set_of_edge v  V E ={w} then (UNIV:real^3->bool) DIFF aff_ge {x,v} {w}
else (UNIV:real^3->bool) DIFF aff {x,v})`;;

 


let azim_fan = new_definition`azim_fan x v w w1= azim x v w w1`;;

let azim_fan1=new_definition`azim_fan1 (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)
= if (CARD (set_of_edges v E) > 1) then azim x v w (sigma_fan x V E v w) else &2* pi`;;


(*
let w_dart0=new_definition`w_dart0 x v w w1 y=(w_dart x V E x v w w1) INTER (rcone_gt x v y)`;;

let c_fan=new_definition`c_fan x v w y ={c | (c IN aff_ge {x} {v,w})/\ (~((c IN rcone_gt x v y)\/(c IN rcone_gt x w y)))}`;; 
*)








(* Proof Lemma 6.1 [AAUHTVE] *)



let node_fan=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) n:num. power_maps n_fan x V E n=power_n_fan x V E n`,
GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[power_maps; n_fan; power_n_fan; power_map_points] THEN INDUCT_TAC THEN REWRITE_TAC[power_maps; power_map_points;i_fan;] THEN REWRITE_TAC[power_map_points; power_maps] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[n_fan;o_funs; pr1; pr2; pr3; pr4]);;





let lem_fan411=prove(`(!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 w:real^3. sigma_fan x V E v (inverse_sigma_fan x V E v w)=w)==> (!x V E. (o_funs (e_fan x V E)(o_funs (n_fan x V E)(f_fan x V E))=i_fan x V E))`, 
REWRITE_TAC[ e_fan; f_fan; n_fan; i_fan; o_funs] THEN 
REWRITE_TAC[pr1; pr2; pr3; pr4] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN ASM_REWRITE_TAC[]);;

let lem_fan412=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool). o_funs (e_fan x V E)  (e_fan x V E) =i_fan x V E`,
REWRITE_TAC[o_funs; e_fan; i_fan;]
THEN REWRITE_TAC[pr1; pr2; pr3; pr4]);;



let e_fan_no_fix_point=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 w:real^3 w1:real^3. (v = w) <=>(e_fan x V E (x,v,w,(sigma_fan x V E v w))=(x,v,w,(sigma_fan x V E v w)))`, 
REPEAT GEN_TAC THEN REWRITE_TAC[e_fan] THEN MESON_TAC[PAIR_EQ] );;

let f_fan_no_fix_point=prove(`!
x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 w:real^3 w1:real^3. (f_fan x V E (x,v,w,(sigma_fan x V E v w))=(x,v,w,(sigma_fan x V E v w)))==>(v=w)`, 
REPEAT GEN_TAC THEN REWRITE_TAC[f_fan] THEN MESON_TAC[PAIR_EQ] );;

let lem_fan4131=prove(`w = power_map_points sigma_fan x V E v w m ==> (x,v,power_map_points sigma_fan x V E v w m,
 sigma_fan x V E v (power_map_points sigma_fan x V E v w m) =
 x,v,w,sigma_fan x V E v w)`, MESON_TAC[]);;

let lem_fan413=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 w:real^3 w1:real^3 n:num m:num. o_funs (power_maps n_fan x V E n)  (e_fan x V E) (x,v,w,w1)=o_funs (e_fan x V E)(power_maps n_fan x V E m) (x,v,w,w1)
==> (power_maps n_fan x V E m) (x,v,w,w1) =(i_fan x V E) (x,v,w,w1)`,
REWRITE_TAC[node_fan; o_funs; e_fan; power_n_fan; i_fan; pr1; pr2; pr3; pr4;] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN 
SUBGOAL_THEN `w=power_map_points sigma_fan x V E v w m` ASSUME_TAC 
THENL [POP_ASSUM MP_TAC THEN MESON_TAC[PAIR_EQ]; 
POP_ASSUM MP_TAC THEN REWRITE_TAC[power_map_points] THEN MESON_TAC[lem_fan4131]]);;


let lem_fan414=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 w:real^3 w1:real^3 n:num. (power_maps n_fan x V E n) (x,v,w,w1)=e_fan x V E (x,v,w,w1)==>(v=w)`, 
REWRITE_TAC[node_fan; e_fan; power_n_fan;]  THEN REPEAT GEN_TAC THEN MESON_TAC[PAIR_EQ]);;





(*-------------------------------------------------------------------------------------------*)
(*    the properties in normal vector                                                        *)
(*-------------------------------------------------------------------------------------------*)
 
let imp_norm_not_zero_fan=prove(`!v:real^3 x:real^3. ~(v = x) ==> ~(norm ( v - x) = &0)`,
REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN `(v:real^3)-(x:real^3)= vec 0` ASSUME_TAC THENL
                   [POP_ASSUM MP_TAC THEN MESON_TAC[NORM_EQ_0];
                    SUBGOAL_THEN `(v:real^3) = (x:real^3)` ASSUME_TAC THENL
                     [POP_ASSUM MP_TAC THEN VECTOR_ARITH_TAC;
                     SET_TAC[]]]);;
let imp_norm_gl_zero_fan=prove(`!v:real^3 x:real^3. ~(v = x) ==> inv(norm ( v - x)) > &0`,
REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `~(norm ( (v:real^3) - (x:real^3)) = &0)` ASSUME_TAC THENL
  [ASM_MESON_TAC[imp_norm_not_zero_fan];
   MP_TAC (ISPEC `(v:real^3)-(x:real^3)` NORM_POS_LE) THEN DISCH_TAC THEN
   SUBGOAL_THEN `norm((v:real^3)-(x:real^3))> &0` ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
      MP_TAC (ISPEC `norm((v:real^3)-(x:real^3))` REAL_LT_INV_EQ) THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]]);;
let imp_inv_norm_not_zero_fan=prove(`!v:real^3 x:real^3. ~(v = x) ==> ~(inv(norm ( v - x)) = &0)`,
REPEAT GEN_TAC THEN DISCH_TAC THEN SUBGOAL_THEN `inv(norm ((v:real^3) - (x:real^3))) > &0` ASSUME_TAC
THENL
  [ASM_MESON_TAC[imp_norm_gl_zero_fan]; 
   POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]);;


let imp_norm_ge_zero_fan=prove(`!v:real^3 x:real^3. ~(v = x) ==> inv(norm ( v - x)) >= &0`,
REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `~(norm ( (v:real^3) - (x:real^3)) = &0)` ASSUME_TAC THENL
  [ASM_MESON_TAC[imp_norm_not_zero_fan];
   MP_TAC (ISPEC `(v:real^3)-(x:real^3)` NORM_POS_LE) THEN DISCH_TAC THEN
   SUBGOAL_THEN `norm((v:real^3)-(x:real^3))> &0` ASSUME_TAC THENL
     [POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
      MP_TAC (ISPEC `norm((v:real^3)-(x:real^3))` REAL_LT_INV_EQ) THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]]);;

let norm_of_normal_vector_is_unit_fan=prove(`!v:real^3 x:real^3. ~(v = x) ==> norm(inv(norm ( v - x))% (v-x))= &1`,
REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[NORM_MUL] THEN SUBGOAL_THEN ` inv(norm ( (v:real^3) - (x:real^3))) >= &0` ASSUME_TAC THENL[ ASM_MESON_TAC[imp_norm_ge_zero_fan]; 
                SUBGOAL_THEN ` ~(norm ( (v:real^3) - (x:real^3))= &0)` ASSUME_TAC THENL
                   [ASM_MESON_TAC[imp_norm_not_zero_fan];
                    SUBGOAL_THEN ` abs(inv(norm ( (v:real^3) - (x:real^3))))= inv(norm ( (v:real^3) - (x:real^3)))` ASSUME_TAC THENL
                       [ASM_MESON_TAC[REAL_ABS_REFL;REAL_ARITH `(a:real)>= &0 <=> &0 <= a`; ];
                        MP_TAC(ISPEC `norm ( (v:real^3) - (x:real^3))` REAL_MUL_LINV)THEN ASM_REWRITE_TAC[]]]]);;



(*---------------------------------------------------------------------------------------*)
(* the normal coordinate                    *)
(*---------------------------------------------------------------------------------------*)
 

let e3_fan=new_definition`e3_fan  (x:real^3) (v:real^3) (u:real^3) = inv(norm((v:real^3)-(x:real^3))) % ((v:real^3)-(x:real^3))`;;




  let e2_fan=new_definition`e2_fan (x:real^3) (v:real^3) (u:real^3) = inv(norm((e3_fan (x:real^3) (v:real^3) (u:real^3)) cross ((u:real^3)-(x:real^3)))) % ((e3_fan (x:real^3) (v:real^3) (u:real^3)) cross ((u:real^3)-(x:real^3))) `;;
  
let e1_fan=new_definition`e1_fan (x:real^3) (v:real^3) (u:real^3)=(e2_fan (x:real^3) (v:real^3) (u:real^3)) cross (e3_fan (x:real^3) (v:real^3) (u:real^3))`;;


  
  let e3_mul_dist_fan=prove(`!x:real^3 v:real^3 u:real^3. ~(v=x) ==> dist (v,x) % e3_fan x v u = v - x`,
REPEAT GEN_TAC THEN REWRITE_TAC[e3_fan; dist; VECTOR_ARITH `(a:real) % (b:real)% (v:real^3)=(a*b)%v`] THEN 
MESON_TAC[imp_norm_not_zero_fan; REAL_MUL_RINV; VECTOR_ARITH `&1 %(v:real^3)=v`]);;

let norm_dot_fan=prove(`!x:real^3. norm x = &1 ==> x dot x = &1`,
 ASM_MESON_TAC[NORM_POW_2; REAL_ARITH `&1 pow 2= &1`]);;


  let e3_is_normal_fan=prove(`!x:real^3 v:real^3 u:real^3. ~(v=x) ==> e3_fan x v u dot e3_fan x v u = &1`,
REPEAT GEN_TAC THEN REWRITE_TAC[e3_fan]THEN DISCH_TAC 
THEN SUBGOAL_THEN `norm(inv(norm((v:real^3)-(x:real^3))) %(v-x)) pow 2= &1 pow 2` ASSUME_TAC THENL
 [ASM_MESON_TAC[norm_of_normal_vector_is_unit_fan] ;
ASM_MESON_TAC[NORM_POW_2; REAL_ARITH `&1 pow 2= &1`]]);;

  let e2_is_normal_fan= prove(`!x:real^3 v:real^3 u:real^3. ~(v=x) /\ ~(u=x) /\ ~(collinear {vec 0, v-x, u-x}) ==> e2_fan x v u dot e2_fan x v u = &1`,
REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `~((e3_fan (x:real^3) (v:real^3) (u:real^3)) cross ((u:real^3)-(x:real^3))= vec 0)` ASSUME_TAC 
THENL[
POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_NOT THEN REWRITE_TAC[e3_fan;CROSS_LMUL] 
THEN DISCH_TAC THEN MP_TAC(ISPECL [`v:real^3`; `x:real^3`] imp_inv_norm_not_zero_fan) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN 
MP_TAC(ISPECL [`inv(norm((v:real^3)-(x:real^3)))`; `((v:real^3) -(x:real^3)) cross ((u:real^3)-(x:real^3))`; `(vec 0):real^3`] VECTOR_MUL_LCANCEL_IMP) 
THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO;CROSS_EQ_0 ];

MP_TAC(ISPECL [`(e3_fan (x:real^3) (v:real^3) (u:real^3)) cross ((u:real^3)-(x:real^3))`; `((vec 0):real^3)`] norm_of_normal_vector_is_unit_fan) THEN 
ASM_REWRITE_TAC[] THEN REWRITE_TAC[e2_fan; VECTOR_ARITH`(v:real^3)- vec 0 = v`] THEN MESON_TAC[norm_dot_fan]]);; 

  let e2_orthogonal_e3_fan=prove(`!x:real^3 v:real^3 u:real^3. 
~(v=x) /\ ~(u=x) /\ ~(collinear {vec 0, v-x, u-x}) ==> (e2_fan x v u) dot (e3_fan x v u)= &0`,
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[e2_fan;e3_fan;CROSS_LMUL;DOT_RMUL;] THEN VEC3_TAC);;



  let e1_is_normal_fan=prove(`!x:real^3 v:real^3 u:real^3. 
~(v=x) /\ ~(u=x) /\ ~(collinear {vec 0, v-x, u-x}) ==> e1_fan x v u dot e1_fan x v u = &1`,
REPEAT GEN_TAC THEN STRIP_TAC THEN 
REWRITE_TAC[e1_fan;DOT_CROSS] THEN 
MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3` ] e2_orthogonal_e3_fan) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN 
MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3` ] e2_is_normal_fan) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN  
MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3` ] e3_is_normal_fan) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

  let e1_orthogonal_e3_fan=prove(`!x:real^3 v:real^3 u:real^3. ~(v=x) /\ ~(u=x) /\ ~(collinear {vec 0, v-x, u-x}) 
==> (e1_fan x v u) dot (e3_fan x v u)= &0`,
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[e1_fan;DOT_CROSS_SELF] );;


  let e1_orthogonal_e2_fan=prove(`!x:real^3 v:real^3 u:real^3. ~(v=x) /\ ~(u=x) /\ ~(collinear {vec 0, v-x, u-x}) 
==> (e1_fan x v u) dot (e2_fan x v u)= &0`,
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[e1_fan;DOT_CROSS_SELF] );;


  let e1_cross_e2_dot_e3_fan=prove(`!x:real^3 v:real^3 u:real^3. ~(v=x) /\ ~(u=x) /\ ~(collinear {vec 0, v-x, u-x}) ==>
&0 < (e1_fan x v u cross e2_fan x v u) dot e3_fan x v u`,
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[e1_fan;CROSS_TRIPLE] 
THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3` ] e1_is_normal_fan) 
THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[e1_fan] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;



  let orthonormal_e1_e2_e3_fan=prove(`!x:real^3 v:real^3 u:real^3. ~(v=x) /\ ~(u=x) /\ ~(collinear {vec 0, v-x, u-x}) ==>
(orthonormal (e1_fan x v u) (e2_fan x v u) (e3_fan x v u))`,

REPEAT GEN_TAC THEN REWRITE_TAC[orthonormal] THEN DISCH_TAC THEN 
ASM_MESON_TAC[e1_is_normal_fan;e2_is_normal_fan;e3_is_normal_fan;e1_orthogonal_e2_fan;
e1_orthogonal_e3_fan;e2_orthogonal_e3_fan;e1_cross_e2_dot_e3_fan]);;



  let dot_e2_fan=prove(`!x:real^3 v:real^3 u:real^3. ~(v=x) /\ ~(u=x) /\ ~(collinear {vec 0, v-x, u-x}) 
==> (u-x) dot e2_fan x v u = &0`,
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[e2_fan;DOT_RMUL;DOT_CROSS_SELF] THEN REAL_ARITH_TAC);;

let vdot_e2_fan=prove(`!x:real^3 v:real^3 u:real^3. ~(v=x) /\ ~(u=x) /\ ~(collinear {vec 0, v-x, u-x}) 
==> (v-x) dot e2_fan x v u = &0`,
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[e2_fan;e3_fan;CROSS_LMUL;DOT_RMUL;DOT_CROSS_SELF] THEN REAL_ARITH_TAC);;

let vcross_e3_fan=prove(`!x:real^3 v:real^3 u:real^3. ~(v=x) /\ ~(u=x) /\ ~(collinear {vec 0, v-x, u-x}) 
==>
(v - x) cross (e3_fan x v u) = vec 0`,

REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[e3_fan;CROSS_RMUL;CROSS_REFL] THEN VECTOR_ARITH_TAC);;

let udot_e1_fan=prove(`!x:real^3 v:real^3 u:real^3. 
~(v=x) /\ ~(u=x) /\ ~(collinear {vec 0, v-x, u-x}) 
==> &0 < (u - x) dot e1_fan x v u `,
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[e1_fan; e2_fan;CROSS_LMUL;DOT_RMUL;DOT_SYM;DOT_LMUL;CROSS_TRIPLE]
THEN SUBGOAL_THEN `~((e3_fan (x:real^3) (v:real^3) (u:real^3)) cross ((u:real^3)-(x:real^3))= vec 0)` ASSUME_TAC
THENL[
POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_NOT THEN REWRITE_TAC[e3_fan;CROSS_LMUL] 
THEN DISCH_TAC THEN MP_TAC(ISPECL [`v:real^3`; `x:real^3`] imp_inv_norm_not_zero_fan) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN 
MP_TAC(ISPECL [`inv(norm((v:real^3)-(x:real^3)))`; `((v:real^3) -(x:real^3)) cross ((u:real^3)-(x:real^3))`; `(vec 0):real^3`] VECTOR_MUL_LCANCEL_IMP) 
THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO;CROSS_EQ_0 ];
MP_TAC(ISPECL [`(e3_fan (x:real^3) (v:real^3) (u:real^3)) cross ((u:real^3)-(x:real^3))`; `((vec 0):real^3)`]imp_norm_gl_zero_fan) THEN 
ASM_REWRITE_TAC[REAL_ARITH`(a:real)> &0 <=> &0 < (a:real)`;VECTOR_ARITH `(a:real^3)- vec 0=a`] THEN DISCH_TAC
  THEN MP_TAC(ISPEC `e3_fan (x:real^3) (v:real^3) (u:real^3) cross (u-x)`DOT_POS_LT) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_MUL]]);;  

let udot_e1_fan1=prove(`!x:real^3 v:real^3 u:real^3. 
~(v=x) /\ ~(u=x) /\ ~(collinear {vec 0, v-x, u-x}) 
==> &0 <= (u - x) dot e1_fan x v u `,
REPEAT GEN_TAC THEN STRIP_TAC THEN 
MP_TAC(ISPECL[`x:real^3` ;`v:real^3` ;`u:real^3`]udot_e1_fan) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);; 


let module_of_vector =prove(`!x:real^3 v:real^3 u:real^3 w:real^3 r:real psi:real h:real.
 ~(v=x) /\ ~(u=x) /\ ~(collinear {vec 0, v-x, u-x}) 
/\ (&0 < r) /\ (w=(r * cos psi) % e1_fan x v u + (r * sin psi) % e2_fan x v u + h % (v-x))
==>
sqrt(((w cross (e3_fan x v u)) dot e1_fan x v u) pow 2 + ((w cross (e3_fan x v u)) dot e2_fan x v u) pow 2) = r`,
REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[CROSS_LADD;CROSS_LMUL;] THEN
MP_TAC(ISPECL [`x:real^3`; `v:real^3`; `u:real^3` ] orthonormal_e1_e2_e3_fan) THEN ASM_REWRITE_TAC[]
  THEN DISCH_THEN (LABEL_TAC "a") THEN 
MP_TAC (ISPECL [`e1_fan (x:real^3) (v:real^3) (u:real^3)`;`e2_fan (x:real^3) (v:real^3) (u:real^3)`;
`e3_fan (x:real^3) (v:real^3) (u:real^3)`]ORTHONORMAL_CROSS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN ASM_REWRITE_TAC[] 
THEN MP_TAC(ISPECL [`x:real^3`; `v:real^3`; `u:real^3` ]vcross_e3_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
  THEN ASM_REWRITE_TAC[]
THEN MP_TAC(ISPECL[`e1_fan (x:real^3) (v:real^3) (u:real^3)`;`e3_fan (x:real^3) (v:real^3) (u:real^3)`]CROSS_SKEW) 
  THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
  THEN REWRITE_TAC[DOT_LADD;DOT_LMUL;DOT_LZERO;DOT_LNEG]
  THEN REMOVE_THEN "a" MP_TAC THEN REWRITE_TAC[orthonormal] THEN  DISCH_TAC THEN ASM_REWRITE_TAC[DOT_SYM]
  THEN REWRITE_TAC[REAL_ARITH `-- &0 = &0`; REAL_ARITH`(a:real)* &0 = &0`; REAL_ARITH `(a:real) * &1 = a`;
REAL_ARITH `(a:real) + &0 = a`;REAL_ARITH `&0 + (a:real) = a`;REAL_POW_MUL; REAL_ARITH `-- &1 pow 2 = &1`;
REAL_ARITH `(d:real) * (b:real) + d * (c:real) = d * ( b + c)`;SIN_CIRCLE; sqrt] THEN MATCH_MP_TAC SELECT_UNIQUE
THEN REWRITE_TAC[BETA_THM] THEN GEN_TAC THEN EQ_TAC

	   THENL[
              STRIP_TAC THEN SUBGOAL_THEN `((y:real) - (r:real))* (y + r) = &0` ASSUME_TAC
	       THENL[
		 REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_ARITH `((a:real)- (b:real)) * (c:real)= a *c - b * c`; 
REAL_ARITH`(y:real) * (r:real)= r * y`; REAL_ARITH `((a:real) +(b:real)) - ((b:real) + (c:real))= a - c`; 
REAL_ARITH `(a:real)- (c:real)= &0 <=> a = c`] 
		   THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
		 MP_TAC (ISPECL [`(y:real)- (r:real)`; `(y:real)+(r:real)` ]REAL_ENTIRE) THEN ASM_REWRITE_TAC[] 
		   THEN STRIP_TAC
		   THENL
		     [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
		     REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC]];

	     DISCH_TAC THEN ASM_REWRITE_TAC[] 
	       THEN REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC]);;




let collinear_imp_azim_is_rezo_fan=prove(
`!x:real^3 v:real^3 u:real^3 y:real h1:real h2:real.
~(v = x) /\ ~(u = x) /\ ~collinear {x, v, u} 
/\ &0 <= y /\
 y < &2 * pi /\
 ( !e1:real^3 e2:real^3 e3:real^3.
          orthonormal e1 e2 e3 /\ dist (v,x) % e3 = v - x
          ==> (?psi:real r1:real r2:real.
                   u - x =
                   (r1 * cos psi) % e1 + (r1 * sin psi) % e2 + h1 % (v - x) /\
                   u - x =
                   (r2 * cos (psi + y)) % e1 +
                   (r2 * sin (psi + y)) % e2 +
                   h2 % (v - x) /\
                   &0 < r1 /\
                   &0 < r2))
 ==> y = &0`,
REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC 
  THEN REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `~collinear {vec 0, (v:real^3)-(x:real^3), (u:real^3)-x}` ASSUME_TAC
  THENL (*1*)[
    POP_ASSUM MP_TAC 
      THEN MATCH_MP_TAC MONO_NOT 
      THEN MP_TAC(ISPECL [`v:real^3`; `x:real^3`; `u:real^3`] COLLINEAR_3) 
      THEN SUBGOAL_THEN `{(v:real^3),(x:real^3),(u:real^3)}={x,v,u}` ASSUME_TAC
      THENL[SET_TAC[]; ASM_REWRITE_TAC[] THEN SET_TAC[]]; (*1*)
   REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC 
     THEN DISCH_THEN (LABEL_TAC "1") THEN DISCH_THEN (LABEL_TAC "2") THEN REWRITE_TAC[LEFT_IMP_FORALL_THM] 
     THEN EXISTS_TAC `e1_fan (x:real^3) (v:real^3) (u:real^3)`
     THEN EXISTS_TAC `e2_fan (x:real^3) (v:real^3) (u:real^3)`
     THEN EXISTS_TAC `e3_fan (x:real^3) (v:real^3) (u:real^3)`
     THEN MP_TAC(ISPECL [`(x:real^3)` ;`(v:real^3)`; `(u:real^3)`] orthonormal_e1_e2_e3_fan) THEN ASM_REWRITE_TAC[] 
     THEN DISCH_TAC
     THEN MP_TAC(ISPECL [`(x:real^3)` ;`(v:real^3)`;`u:real^3`] e3_mul_dist_fan)THEN ASM_REWRITE_TAC[] 
     THEN DISCH_THEN(LABEL_TAC "AB") THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
     THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`; `(u:real^3)- (x:real^3)`; `r1:real`; `psi:real`; `h1:real`] module_of_vector) 
     THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
     THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`; `(u:real^3)- (x:real^3)`; `r2:real`; `(psi:real)+(y:real)`; `h2:real`] module_of_vector)  
     THEN ASM_REWRITE_TAC[]
     THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC 
     THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC
     THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC 
     THEN ASM_REWRITE_TAC[] THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
     THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC  THEN POP_ASSUM MP_TAC
     THEN POP_ASSUM (fun th-> REWRITE_TAC[SYM(th)] THEN ASSUME_TAC th)
     THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN `sin (psi:real)= &0` ASSUME_TAC
      THENL (*2*)[
	MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] dot_e2_fan) 
	  THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[DOT_LADD;DOT_LMUL] 
	  THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] vdot_e2_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
	  THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] e2_is_normal_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
	  THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] e1_orthogonal_e2_fan) 
	  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
	  THEN ASM_REWRITE_TAC[] 
	  THEN REWRITE_TAC[REAL_ARITH`(a:real)* &0 = &0`; REAL_ARITH`(a:real)+ &0= a`; REAL_ARITH`&0 + (a:real)= a`; 
               REAL_ARITH`(a:real) * &1= a`]
	  THEN DISCH_TAC
	  THEN MATCH_MP_TAC(ISPECL [`sin (psi:real)`;`&0`; `r1:real`] REAL_EQ_LCANCEL_IMP)  THEN ASM_REWRITE_TAC[] 
	  THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC; (*2*)


	POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC 
	  THEN POP_ASSUM MP_TAC  THEN POP_ASSUM MP_TAC 
	  THEN DISCH_THEN (LABEL_TAC "a")   THEN DISCH_THEN (LABEL_TAC "b")
	  THEN REPEAT (DISCH_TAC) THEN REMOVE_THEN "a" MP_TAC THEN REMOVE_THEN "b" MP_TAC
	  THEN REWRITE_TAC[COS_ADD;SIN_ADD] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
	  THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] dot_e2_fan) 
	  THEN ASM_REWRITE_TAC[] THEN  REWRITE_TAC[DOT_LADD;DOT_LMUL] 
	  THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] vdot_e2_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
	  THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] e2_is_normal_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
	  THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] e1_orthogonal_e2_fan) 
	  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
	  THEN ASM_REWRITE_TAC[] 
	  THEN REWRITE_TAC[REAL_ARITH`(a:real)* &0 = &0`; REAL_ARITH`&0 * (a:real) = &0`; 
              REAL_ARITH`(a:real)+ &0= a`; REAL_ARITH`&0 + (a:real)= a`; REAL_ARITH`(a:real) * &1= a`;REAL_ENTIRE] 
	  THEN ASM_REWRITE_TAC[]
	  THEN DISCH_THEN(LABEL_TAC "a") THEN DISCH_TAC THEN REMOVE_THEN "a" MP_TAC
	  THEN STRIP_TAC
	     THENL(*3*)[
	       REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;(*3*)
	       MP_TAC(ISPEC `psi:real` SIN_CIRCLE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;(*3*)
	       MP_TAC(ISPEC `y:real` SIN_EQ_0) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN POP_ASSUM MP_TAC 
		 THEN POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC "3") THEN DISCH_TAC THEN REMOVE_THEN "1" MP_TAC 
		 THEN REMOVE_THEN "2" MP_TAC THEN ASM_REWRITE_TAC[] THEN MP_TAC(PI_WORKS) THEN REPEAT STRIP_TAC 
		 THEN MP_TAC(ISPECL [ `n:real`;`&2`;`pi:real`]REAL_LT_RCANCEL_IMP) 
		 THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "4")
		 THEN MP_TAC(ISPECL [ `&0`;`n:real`;`pi:real`]REAL_LE_RCANCEL_IMP) 
		 THEN REWRITE_TAC[REAL_ARITH`&0 * (a:real) = &0`] 
		 THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "5")  
		 THEN MP_TAC(ISPECL [`n:real`; `pi:real`]REAL_ENTIRE) THEN DISCH_TAC THEN ASM_REWRITE_TAC[]  
		 THEN REMOVE_THEN "3" MP_TAC THEN REWRITE_TAC[integer] 
		 THEN MP_TAC(ISPEC `n:real` REAL_ABS_REFL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
		 THEN STRIP_TAC THEN REMOVE_THEN "4" MP_TAC THEN REMOVE_THEN "5" MP_TAC 
		 THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC
		 THEN MP_TAC(ISPECL [`0`; `n':num`]REAL_OF_NUM_LE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
		 THEN MP_TAC(ISPECL [`n':num`; `2`]REAL_OF_NUM_LT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
		 THEN SUBGOAL_THEN `(n':num)= 0 \/ n' = 1` ASSUME_TAC
		    THENL (*4*)[
		      POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;(*4*)
		      POP_ASSUM MP_TAC THEN STRIP_TAC
			THENL(*5*)[
			  ASM_MESON_TAC[REAL_OF_NUM_EQ];(*5*)
			  POP_ASSUM MP_TAC THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
			    THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
			    THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
			    THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
			    THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "A") THEN REPEAT DISCH_TAC 
			    THEN REMOVE_THEN "A" MP_TAC 
			    THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
			    THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
			    THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
			    THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
			    THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
			    THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
			    THEN POP_ASSUM (fun th-> REWRITE_TAC[th])

			    THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "A") THEN REPEAT DISCH_TAC 
			    THEN REMOVE_THEN "A" MP_TAC 
			    THEN POP_ASSUM MP_TAC 
			    THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "A") THEN REPEAT DISCH_TAC 
			    THEN REMOVE_THEN "A" MP_TAC THEN ASM_REWRITE_TAC[] 
			    THEN REWRITE_TAC[REAL_ARITH `&1 * (a:real)=a`]
			    THEN POP_ASSUM MP_TAC 
			    THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
			    THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
			    THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "A") THEN REPEAT DISCH_TAC 
			    THEN REMOVE_THEN "A" MP_TAC THEN ASM_REWRITE_TAC[]
			    THEN REWRITE_TAC[SIN_PI;COS_PI; REAL_ARITH `(a:real)- &0 = a`; REAL_ARITH `(a:real) * &0= &0`;
				REAL_ARITH `(a:real) * -- &1= -- a`;
				VECTOR_ARITH `&0 % (v:real^3)= vec 0`; VECTOR_ARITH `(v:real^3)+ vec 0 + (w:real^3)= v+w`]
			    THEN REMOVE_THEN "AB" MP_TAC THEN DISCH_TAC 
			    THEN POP_ASSUM (fun th -> REWRITE_TAC[SYM(th)]) THEN DISCH_TAC 
			    THEN SUBGOAL_THEN `(((r2:real) * --cos (psi:real)) % e1_fan (x:real^3) (v:real^3) (u:real^3) + (h2:real) % dist (v,x) % e3_fan x v u) dot e1_fan x v u =(((r2:real) * cos psi) % e1_fan x v u + (h1:real) % dist (v,x) % e3_fan x v u) dot e1_fan x v u` ASSUME_TAC
			    THENL (*6*)[
			      ASM_REWRITE_TAC[]; (*6*)
			      POP_ASSUM MP_TAC THEN REWRITE_TAC[DOT_LADD;DOT_LMUL;DOT_SYM;]
				THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] e1_is_normal_fan) 
				THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
				THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] e1_orthogonal_e3_fan) 
				THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
				THEN ASM_REWRITE_TAC[] 
				THEN REWRITE_TAC[REAL_ARITH `(a:real) * &0 = &0`; REAL_ARITH `(a:real)+ &0=a`; 
						 REAL_ARITH `(a:real) * &1 =a`; 
						 REAL_ARITH `(a:real) *(-- b)= a * b <=> &2 * a * b = &0`]
				THEN DISCH_TAC 
				THEN MP_TAC(ISPECL [`&2 * (r2:real)`; `cos (psi:real)`]REAL_ENTIRE) 
				THEN REWRITE_TAC[REAL_ARITH `((a:real)*(b:real))*(c:real)=a * b * c`] 
				THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
				 THENL(*7*)[
				   REPEAT(POP_ASSUM MP_TAC ) THEN REAL_ARITH_TAC;(*7*)
				   MP_TAC( ISPEC `psi:real` SIN_CIRCLE) 
				     THEN ASM_REWRITE_TAC[] 
				     THEN REWRITE_TAC[REAL_ARITH `&0 pow 2= &0`; REAL_ARITH `&0 + &0 = &0`] 
				     THEN SET_TAC[](*7*)](*6*)](*5*)]]]]]);;




let azim_is_zero_fan=prove(`!x:real^3 v:real^3 u:real^3. 
~(v=x) /\ ~(u=x) /\ (~(collinear {x, v, u}))
==>
azim (x:real^3) (v:real^3) (u:real^3) (u:real^3) = &0`,
REPEAT GEN_TAC THEN STRIP_TAC THEN
REWRITE_TAC[azim_def] THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SELECT_UNIQUE 
THEN REWRITE_TAC[BETA_THM] THEN GEN_TAC THEN EQ_TAC
THENL[
  REPEAT STRIP_TAC 
    THEN MP_TAC (ISPECL[`x:real^3`; `v:real^3`; `u:real^3`; `y:real`; `h1:real`; `h2:real`]collinear_imp_azim_is_rezo_fan) 
    THEN ASM_REWRITE_TAC[]; 
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
    THENL[
      REAL_ARITH_TAC; 
      STRIP_TAC
	THENL[
	  ASSUME_TAC(PI_WORKS) THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
	  MP_TAC(ISPECL [`x:real^3`; `v:real^3`; `u:real^3`; `u:real^3`] AZIM_EXISTS)
	    THEN ASM_REWRITE_TAC[]  
	    THEN STRIP_TAC 
	    THEN EXISTS_TAC `h1:real` 
	    THEN EXISTS_TAC `h2:real`
	    THEN MP_TAC (ISPECL[`x:real^3`; `v:real^3`; `u:real^3`; `theta:real`; `h1:real`; `h2:real`]collinear_imp_azim_is_rezo_fan) 
	    THEN ASM_REWRITE_TAC[]
	    THEN POP_ASSUM MP_TAC  
	    THEN DISCH_THEN(LABEL_TAC "a") THEN DISCH_THEN (LABEL_TAC "b")
	    THEN REMOVE_THEN "a" MP_TAC THEN ASM_REWRITE_TAC[]]]]);;


let property_of_cyclic_set=prove(`!x:real^3 v:real^3 u:real^3 w1:real^3 w2:real^3.
 cyclic_set {u, w1, w2} x v
==> ~(v=x) /\ ~(u=x)/\ ~collinear {vec 0, v-x, u-x}`,

(let th= prove(`!x:real^3 v:real^3 u:real^3 w1:real^3 w2:real^3.
x IN {x,w1,w2}`, SET_TAC[]) in

(let th1=prove(`!x:real^3 v:real^3 u:real^3 w1:real^3 w2:real^3.
x IN  affine hull {x,v}
`,REPEAT GEN_TAC THEN REWRITE_TAC[AFFINE_HULL_2;INTER; IN_ELIM_THM] THEN EXISTS_TAC`&1` THEN EXISTS_TAC `&0` THEN
 MESON_TAC[REAL_ARITH`&1+ &0= &1`; VECTOR_ARITH`x= &1 % x + &0 % v`])
in

(let th2=prove(`!x:real^3 v:real^3 u:real^3 w1:real^3 w2:real^3.
x IN {x,w1,w2} INTER affine hull {x,v}
`, REWRITE_TAC[INTER;IN_ELIM_THM] THEN REWRITE_TAC[th;th1]) in


REPEAT GEN_TAC THEN 
REWRITE_TAC[COLLINEAR_LEMMA;DE_MORGAN_THM;VECTOR_ARITH`a-b=vec 0 <=> a=b`;cyclic_set;] THEN STRIP_TAC 
  THEN ASM_REWRITE_TAC[VECTOR_ARITH`(v:real^3)=(x:real^3) <=> x=v`] THEN STRIP_TAC
THENL[ STRIP_TAC  THEN
  POP_ASSUM MP_TAC  THEN POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC"a")  THEN DISCH_TAC 
THEN REMOVE_THEN "a" MP_TAC THEN ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL[`x:real^3`; `v:real^3`; `u:real^3`; `w1:real^3`; `w2:real^3`] th2) THEN SET_TAC[];

STRIP_TAC THENL[

STRIP_TAC  THEN
  POP_ASSUM MP_TAC  THEN POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC"a")  THEN DISCH_TAC 
THEN REMOVE_THEN "a" MP_TAC THEN ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL[`x:real^3`; `v:real^3`; `u:real^3`; `w1:real^3`; `w2:real^3`] th2) THEN SET_TAC[];

STRIP_TAC THEN POP_ASSUM MP_TAC  THEN POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC"a")  THEN DISCH_TAC 
THEN REMOVE_THEN "a" MP_TAC THEN POP_ASSUM MP_TAC 
THEN REWRITE_TAC[VECTOR_ARITH`(c:real) % ((v:real^3)-(x:real^3))=(u:real^3)-x <=> u =  (&1 - c) % x+c % v`] 

THEN DISCH_TAC THEN SUBGOAL_THEN `(u:real^3) IN affine hull {(x:real^3),(v:real^3)}` ASSUME_TAC
THENL[
REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN EXISTS_TAC `&1 - (c:real)` THEN EXISTS_TAC`c:real`
THEN ASM_REWRITE_TAC[REAL_ARITH`&1 - (c:real) +c= &1`;];

MP_TAC(ISPECL[`u:real^3`; `v:real^3`; `u:real^3`; `w1:real^3`; `w2:real^3`]th) THEN DISCH_TAC THEN SET_TAC[INTER]
]]]))));;


let property_of_cyclic_set1=prove(`!x:real^3 v:real^3 u:real^3 w1:real^3 w2:real^3.
 cyclic_set {u, w1, w2} x v
==> ~collinear {x, v, w1}`,
				 
(let th=prove(`{u,w1,w2}={w1,u,w2}`,SET_TAC[]) in

REPEAT GEN_TAC THEN DISCH_TAC 
THEN MP_TAC (SPECL [`x:real^3`; `v:real^3`; `w1:real^3`;`u:real^3`; `w2:real^3`] property_of_cyclic_set) THEN ASM_REWRITE_TAC[th] THEN STRIP_TAC THEN ASM_REWRITE_TAC[COLLINEAR_3]));;

let property_of_cyclic_set2=prove(`!x:real^3 v:real^3 u:real^3 w1:real^3 w2:real^3.
 cyclic_set {u, w1, w2} x v
==> ~collinear {x, v, w2}`,			 
( let th=prove(`{u,w1,w2}={w2,w1,u}`,SET_TAC[]) in
( let th1=prove(`{u,w1,w2}={w1,w2,u}`,SET_TAC[]) in

REPEAT GEN_TAC THEN DISCH_TAC 
THEN MP_TAC (SPECL [`x:real^3`; `v:real^3`; `w2:real^3`;`w1:real^3`; `u:real^3`] property_of_cyclic_set)
THEN ASM_REWRITE_TAC[th] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN MESON_TAC[th1;COLLINEAR_3])));;

let SINCOS_PRINCIPAL_VALUE_FAN = prove(
`!x:real. ?y:real. (&0<= y /\ y < &2* pi) /\ (sin(y) = sin(x) /\ cos(y) = cos(x))`,
  GEN_TAC THEN MP_TAC(SPECL [`x:real`] SINCOS_PRINCIPAL_VALUE) THEN STRIP_TAC THEN
DISJ_CASES_TAC(REAL_ARITH`((y:real) < &0)\/ (&0 <= y)`) THENL
[ EXISTS_TAC `(y:real)+ &2 * pi` THEN ASSUME_TAC(PI_POS) 
THEN ASM_REWRITE_TAC[SIN_PERIODIC;COS_PERIODIC] THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
 EXISTS_TAC `(y:real)` THEN ASSUME_TAC(PI_POS) 
THEN ASM_REWRITE_TAC[] THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC]);;

let sin_of_u_fan=prove(`!x:real^3 v:real^3 u:real^3 r1:real psi:real h1:real.
  ~collinear {u,x,v} /\ ~(v=x) /\ ~(u=x)/\ ~collinear {vec 0, v-x, u-x} /\ &0 < r1 
/\ u - x = (r1 * cos psi) % (e1_fan x v u) + (r1 * sin psi) % (e2_fan x v u) + h1 % (v-x)
==> sin psi = &0`,
REPEAT GEN_TAC THEN STRIP_TAC THEN  MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] dot_e2_fan) 
	  THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[DOT_LADD;DOT_LMUL] 
	  THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] vdot_e2_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
	  THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] e2_is_normal_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
	  THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] e1_orthogonal_e2_fan) 
	  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
	  THEN ASM_REWRITE_TAC[]
          THEN REWRITE_TAC[REAL_ARITH`(a:real)* &0 = &0`; REAL_ARITH`(a:real)+ &0= a`; REAL_ARITH`&0 + (a:real)= a`; 
               REAL_ARITH`(a:real) * &1= a`]
	  THEN DISCH_TAC
          THEN MATCH_MP_TAC(ISPECL [`sin (psi:real)`;`&0`; `r1:real`] REAL_EQ_LCANCEL_IMP)  THEN ASM_REWRITE_TAC[] 
	  THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

let cos_of_u_fan=prove(`!x:real^3 v:real^3 u:real^3 r1:real psi:real h1:real.
  ~collinear {u,x,v} /\ ~(v=x) /\ ~(u=x)/\ ~collinear {vec 0, v-x, u-x} /\ &0 < r1 
/\ u - x = (r1 * cos psi) % (e1_fan x v u) + (r1 * sin psi) % (e2_fan x v u) + h1 % (v-x)
==> cos psi = &1`,
REPEAT GEN_TAC THEN STRIP_TAC 
THEN MP_TAC(ISPECL[`x:real^3`; `v:real^3`; `u:real^3`; `(u:real^3)-(x:real^3)`; `r1:real`; `psi:real`; `h1:real`]module_of_vector) THEN ASM_REWRITE_TAC[] THEN 
 POP_ASSUM (fun th-> REWRITE_TAC[SYM(th)] THEN ASSUME_TAC(th))
THEN POP_ASSUM MP_TAC
  THEN MP_TAC(ISPECL[`(u:real^3)-(x:real^3)`; `e3_fan (x:real^3) (v:real^3)(u:real^3)`;`e1_fan (x:real^3) (v:real^3)(u:real^3)`]CROSS_TRIPLE) THEN DISCH_TAC THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
THEN MP_TAC(ISPECL[`(u:real^3)-(x:real^3)`; `e3_fan (x:real^3) (v:real^3)(u:real^3)`;`e2_fan (x:real^3) (v:real^3)(u:real^3)`]CROSS_TRIPLE) THEN DISCH_TAC THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
 THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] orthonormal_e1_e2_e3_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
  THEN
MP_TAC(ISPECL[`e1_fan (x:real^3) (v:real^3)(u:real^3)`; `e2_fan (x:real^3) (v:real^3)(u:real^3)`;`e3_fan (x:real^3) (v:real^3)(u:real^3)`]ORTHONORMAL_CROSS )THEN POP_ASSUM (fun th-> REWRITE_TAC[th]) THEN STRIP_TAC THEN 
POP_ASSUM (fun th-> REWRITE_TAC[th]) THEN POP_ASSUM (fun th-> REWRITE_TAC[th]) THEN
POP_ASSUM (fun th-> REWRITE_TAC[CROSS_SKEW;th])
  THEN MP_TAC(ISPECL[`x:real^3`; `v:real^3`; `u:real^3`] dot_e2_fan)THEN ASM_REWRITE_TAC[]
THEN DISCH_TAC THEN MP_TAC(ISPECL[ `e2_fan (x:real^3) (v:real^3)(u:real^3)`;`(u:real^3)-(x:real^3)`]DOT_SYM) THEN DISCH_TAC THEN ASM_REWRITE_TAC[REAL_ARITH`&0 pow 2 +(a:real)=a`] THEN
MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`] udot_e1_fan1) THEN ASM_REWRITE_TAC[DOT_LNEG;] THEN DISCH_TAC 
  THEN  MP_TAC(ISPECL[ `e1_fan (x:real^3) (v:real^3)(u:real^3)`;`(u:real^3)-(x:real^3)`]DOT_SYM) THEN DISCH_TAC THEN
POP_ASSUM (fun th-> REWRITE_TAC[th]) THEN REWRITE_TAC[POW_2_SQRT_ABS;REAL_ABS_NEG] THEN
 MP_TAC(ISPECL[ `((u:real^3)-(x:real^3)) dot e1_fan (x:real^3) (v:real^3)(u:real^3)`]
  REAL_ABS_REFL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] 
  THEN DISCH_THEN (LABEL_TAC "a") THEN DISCH_TAC
THEN
 MP_TAC(ISPECL[`x:real^3`; `v:real^3`; `u:real^3`; `r1:real`; `psi:real`; `h1:real`] sin_of_u_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REMOVE_THEN "a" MP_TAC THEN ASM_REWRITE_TAC[VECTOR_ARITH`
 (r1 * cos psi) % e1_fan x v u + (r1 * &0) % e2_fan x v u + h1 % (v - x)=
 (r1 * cos psi) % e1_fan x v u + h1 % (v - x)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN`((u:real^3) - (x:real^3)) dot e1_fan x (v:real^3) u = (((r1:real) * cos (psi:real)) % e1_fan x v u + (h1:real) % (v - x)) dot e1_fan x v u` ASSUME_TAC

THENL[ASM_MESON_TAC[];

POP_ASSUM MP_TAC THEN REWRITE_TAC[DOT_LADD;DOT_LMUL] THEN POP_ASSUM MP_TAC THEN  MP_TAC(ISPECL[`x:real^3`;`v:real^3`;`u:real^3`]e3_mul_dist_fan) THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC
THEN POP_ASSUM (fun th-> REWRITE_TAC[SYM(th)])
THEN MP_TAC(ISPECL[`x:real^3`;`v:real^3`;`u:real^3`]
e1_orthogonal_e3_fan) THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC THEN ASM_REWRITE_TAC[DOT_LMUL;DOT_SYM]
THEN MP_TAC(ISPECL[`x:real^3`;`v:real^3`;`u:real^3`]
e1_is_normal_fan) THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC THEN ASM_REWRITE_TAC[REAL_ARITH`(a:real)* &1+ (b:real)*(c:real)* &0= a`] THEN REPEAT DISCH_TAC 
  THEN MP_TAC(ISPECL[`&1`;`cos (psi:real)`; `r1:real`]REAL_EQ_LCANCEL_IMP) THEN REWRITE_TAC[REAL_ARITH`(a:real)* &1=a`; REAL_ARITH`&1 = (a:real) <=> a= &1`] THEN DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC]);;


 

let sincos_of_u_fan=prove(`!x:real^3 v:real^3 u:real^3 r1:real psi:real h1:real.
  ~collinear {u,x,v} /\ ~(v=x) /\ ~(u=x)/\ ~collinear {vec 0, v-x, u-x} /\ &0 < r1 
/\ u - x = (r1 * cos psi) % (e1_fan x v u) + (r1 * sin psi) % (e2_fan x v u) + h1 % (v-x)
==>  sin psi = &0 /\ cos psi = &1`,
MESON_TAC[cos_of_u_fan;sin_of_u_fan]);;










let sum1_azim_fan=prove(`!x:real^3 v:real^3 u:real^3 w1:real^3 w2:real^3.
 cyclic_set {u, w1, w2} x v /\ azim x v u w1 + azim x v w1 w2 < &2 * pi
==> 
azim x v u w2 = azim x v u w1+ azim x v w1 w2
`,
( let th=prove(`!x v u. {v,x,u}={x,v,u}/\{v,x,u}={u,x,v}`,SET_TAC[]) in  


REPEAT GEN_TAC THEN STRIP_TAC 
THEN MP_TAC (SPECL [`x:real^3`; `v:real^3`; `u:real^3`;`w1:real^3`; `w2:real^3`] property_of_cyclic_set) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
MP_TAC (SPECL [`x:real^3`; `v:real^3`; `u:real^3`;`w1:real^3`; `w2:real^3`] property_of_cyclic_set1) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC (SPECL [`x:real^3`; `v:real^3`; `u:real^3`;`w1:real^3`; `w2:real^3`] property_of_cyclic_set2) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`v:real^3`; `x:real^3`; `u:real^3`]COLLINEAR_3) THEN ASM_REWRITE_TAC[] THEN
DISCH_TAC THEN  SUBGOAL_THEN `~collinear {(x:real^3),(v:real^3),(u:real^3)}/\ ~collinear {(u:real^3),(x:real^3),(v:real^3)}` ASSUME_TAC
THENL[ASM_MESON_TAC[th];

MP_TAC (SPECL [`x:real^3`; `v:real^3`; `w1:real^3`; `w2:real^3`] azim) 
  THEN STRIP_TAC 
THEN POP_ASSUM(MP_TAC o SPECL [`e1_fan (x:real^3) (v:real^3) (u:real^3)`;`e2_fan (x:real^3) (v:real^3) (u:real^3)`;`e3_fan (x:real^3) (v:real^3) (u:real^3)`]) 
  THEN MP_TAC(ISPECL[`(x:real^3)`; `(v:real^3)`; `(u:real^3)`] orthonormal_e1_e2_e3_fan) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
MP_TAC(ISPECL[`(x:real^3)`; `(v:real^3)`; `(u:real^3)`] e3_mul_dist_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
  THEN MP_TAC(SPEC `psi:real` SINCOS_PRINCIPAL_VALUE_FAN ) THEN STRIP_TAC THEN
MP_TAC(ISPECL[`x:real^3`;`v:real^3`;`u:real^3`;`u:real^3`]AZIM_EXISTS) THEN STRIP_TAC 
THEN
POP_ASSUM (fun th-> MP_TAC (ISPECL[`e1_fan (x:real^3) (v:real^3) (u:real^3)`;`e2_fan (x:real^3) (v:real^3) (u:real^3)`;`e3_fan (x:real^3) (v:real^3) (u:real^3)`]th)) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC
  THEN MP_TAC(ISPECL[`x:real^3`; `v:real^3`; `u:real^3` ;`r1':real`; `psi':real`; `h1':real`]sincos_of_u_fan)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 

THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`; `w1:real^3`; `h1':real`; `h1:real`; `r1':real`; `r1:real`;
`e1_fan (x:real^3) (v:real^3) (u:real^3)`;`e2_fan (x:real^3) (v:real^3) (u:real^3)`;`e3_fan (x:real^3) (v:real^3) (u:real^3)`; `psi':real`; `y:real`  ] AZIM_UNIQUE)
  THEN ASM_REWRITE_TAC[COS_ADD;SIN_ADD;REAL_ARITH` &1 * (a:real) - &0 * (b:real)=a`;REAL_ARITH`&0 * (a:real) + &1 * (b:real)=b`]
THEN DISCH_TAC THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `u:real^3`; `w2:real^3`; `h1':real`; `h2:real`; `r1':real`; `r2:real`;
`e1_fan (x:real^3) (v:real^3) (u:real^3)`;`e2_fan (x:real^3) (v:real^3) (u:real^3)`;`e3_fan (x:real^3) (v:real^3) (u:real^3)`; `psi':real`; `azim (x:real^3) (v:real^3) (u:real^3) (w1:real^3) + azim x v w1 (w2:real^3)`  ] AZIM_UNIQUE) 
THEN DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THENL[ ASM_MESON_TAC[REAL_LE_ADD];


ASM_REWRITE_TAC[COS_ADD;SIN_ADD;REAL_ARITH` &1 * (a:real) - &0 * (b:real)=a`;REAL_ARITH`&0 * (a:real) + &1 * (b:real)=b`]
     ]]));;






let sum2_azim_fan=prove(`!x:real^3 v:real^3 u:real^3 w1:real^3 w2:real^3.
 cyclic_set {u, w1, w2} x v /\ azim x v u w1 <= azim x v u w2
==> 
azim x v u w2 = azim x v u w1 + azim x v w1 w2
`,

(let th=prove(`!x v u. {v,x,u}={x,v,u}/\{v,x,u}={u,x,v}`,SET_TAC[]) in

REWRITE_TAC[REAL_ARITH`(a:real)=(b:real)+(c:real) <=> c=a-b`] THEN
REPEAT GEN_TAC THEN STRIP_TAC 
THEN MP_TAC (SPECL [`x:real^3`; `v:real^3`; `u:real^3`;`w1:real^3`; `w2:real^3`] property_of_cyclic_set) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
MP_TAC (SPECL [`x:real^3`; `v:real^3`; `u:real^3`;`w1:real^3`; `w2:real^3`] property_of_cyclic_set1) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC (SPECL [`x:real^3`; `v:real^3`; `u:real^3`;`w1:real^3`; `w2:real^3`] property_of_cyclic_set2) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`v:real^3`; `x:real^3`; `u:real^3`]COLLINEAR_3) THEN ASM_REWRITE_TAC[] THEN
DISCH_TAC THEN  SUBGOAL_THEN `~collinear {(x:real^3),(v:real^3),(u:real^3)}/\ ~collinear {(u:real^3),(x:real^3),(v:real^3)}` ASSUME_TAC
THENL[ASM_MESON_TAC[th];
MP_TAC (SPECL [`x:real^3`; `v:real^3`; `u:real^3`; `w1:real^3`] azim) 
  THEN STRIP_TAC 
THEN POP_ASSUM(MP_TAC o SPECL [`e1_fan (x:real^3) (v:real^3) (u:real^3)`;`e2_fan (x:real^3) (v:real^3) (u:real^3)`;`e3_fan (x:real^3) (v:real^3) (u:real^3)`]) 
THEN MP_TAC (SPECL [`x:real^3`; `v:real^3`; `u:real^3`; `w2:real^3`] azim) THEN STRIP_TAC 
THEN POP_ASSUM(MP_TAC o SPECL [`e1_fan (x:real^3) (v:real^3) (u:real^3)`;`e2_fan (x:real^3) (v:real^3) (u:real^3)`;`e3_fan (x:real^3) (v:real^3) (u:real^3)`]) 
THEN MP_TAC(ISPECL[`(x:real^3)`; `(v:real^3)`; `(u:real^3)`] orthonormal_e1_e2_e3_fan) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
MP_TAC(ISPECL[`(x:real^3)`; `(v:real^3)`; `(u:real^3)`] e3_mul_dist_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
  THEN ASM_REWRITE_TAC[]
THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC 
  THEN DISCH_THEN (LABEL_TAC"a") THEN DISCH_THEN (LABEL_TAC"b")
THEN REPEAT STRIP_TAC
   THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC
  THEN DISCH_THEN (LABEL_TAC"c") THEN REPEAT STRIP_TAC 
  THEN MP_TAC(ISPECL[`x:real^3`; `v:real^3`; `u:real^3` ;`r1:real`; `psi:real`; `h1':real`]sincos_of_u_fan)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC(ISPECL[`x:real^3`; `v:real^3`; `u:real^3` ;`r1':real`; `psi':real`; `h1:real`]sincos_of_u_fan)
  THEN REMOVE_THEN "a" MP_TAC THEN ASM_REWRITE_TAC[] THEN  DISCH_TAC THEN DISCH_TAC
  THEN REMOVE_THEN "b" MP_TAC THEN REMOVE_THEN "c" MP_TAC
  THEN ASM_REWRITE_TAC[COS_ADD;SIN_ADD;REAL_ARITH` &1 * (a:real) - &0 * (b:real)=a`;REAL_ARITH`&0 * (a:real) + &1 * (b:real)=b`]
  THEN REPEAT STRIP_TAC 
  THEN MP_TAC (ISPECL [`x:real^3`; `v:real^3`; `w1:real^3`; `w2:real^3`; `h2:real`; `h2':real`; `r2':real`; `r2:real`;
`e1_fan (x:real^3) (v:real^3) (u:real^3)`;`e2_fan (x:real^3) (v:real^3) (u:real^3)`;`e3_fan (x:real^3) (v:real^3) (u:real^3)`; `azim (x:real^3) (v:real^3) (u:real^3) (w1:real^3)`; `azim (x:real^3) (v:real^3) (u:real^3) (w2:real^3) - azim x v u (w1:real^3)`  ] AZIM_UNIQUE) 
THEN DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC 
THEN ASM_REWRITE_TAC[REAL_ARITH`(a:real)+(b:real)-a=b`; REAL_ARITH`(&0 <= (a:real)-(b:real))<=> b<= a`] THEN MP_TAC(ISPEC `azim (x:real^3) (v:real^3) (u:real^3) (w1:real^3)` REAL_NEG_LE0) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
THEN MP_TAC(ISPECL[`azim (x:real^3) (v:real^3) (u:real^3) (w2:real^3)`;`&2 * pi`;`--azim (x:real^3) (v:real^3) (u:real^3) (w1:real^3)`;`&0`]REAL_LTE_ADD2 ) 
THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]));;



let  SUR_SIGMA_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (w:real^3).
FAN(x,V,E) /\ ({v,u} IN E)
==> ?w.  {v,w} IN E /\sigma_fan x V E v w= u
`,
REPEAT GEN_TAC THEN STRIP_TAC 
THEN DISJ_CASES_TAC(SET_RULE `(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={(u:real^3)})\/ ~(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={(u:real^3)})`)
THENL(*1*)[
EXISTS_TAC`u:real^3` THEN ASM_REWRITE_TAC[sigma_fan];(*1*)

MP_TAC(ISPECL[`(x:real^3) `;`(V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]properties_of_set_of_edge_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
MP_TAC(ISPECL[`(x:real^3) `;`(V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]exists_inverse_sigma_fan) THEN ASM_REWRITE_TAC[azim1;] THEN STRIP_TAC THEN
MP_TAC(ISPECL[`(x:real^3) `;`(V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (w:real^3)`]properties_of_set_of_edge_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[] 
  THEN MATCH_MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (w:real^3)`;` (u:real^3)`] UNIQUE_SIGMA_FAN)
  THEN ASM_REWRITE_TAC[] 
  THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC "be") THEN DISCH_TAC
THEN DISJ_CASES_TAC(SET_RULE`set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={w} \/ ~(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={w})`)
THENL(*2*)[
FIND_ASSUM(MP_TAC)`u:real^3 IN set_of_edge v V E` THEN POP_ASSUM(fun th->REWRITE_TAC[th;IN_SING]) THEN SET_TAC[] ;(*2*)

ASM_REWRITE_TAC[] THEN GEN_TAC THEN STRIP_TAC THEN
DISJ_CASES_TAC(SET_RULE`~(azim (x:real^3) v w u <= azim x v w w1)\/ (azim (x:real^3) v w u <= azim x v w w1)`)
THENL(*3*)[
ASM_REWRITE_TAC[] THEN SUBGOAL_THEN`azim (x:real^3) v w w1 <= azim x v w u` ASSUME_TAC
THENL(*4*)[
POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;(*4*)
 SUBGOAL_THEN `{(w:real^3),(w1:real^3),(u:real^3)} SUBSET set_of_edge v V E` ASSUME_TAC
THENL(*5*)[
SET_TAC[];(*5*)
FIND_ASSUM(MP_TAC)`FAN((x:real^3),V,E)` THEN REWRITE_TAC[FAN;fan6] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "b") THEN STRIP_TAC THEN
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (u:real^3)`;` (v:real^3)`]properties_of_graph) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`]CYCLIC_SET_EDGE_FAN) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;`{(w:real^3), (w1:real^3),(u:real^3)}`;`set_of_edge(v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)` ]subset_cyclic_set_fan)
		THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`x:real^3`;`v:real^3`;`w:real^3`;`w1:real^3`;`u:real^3`]sum2_azim_fan) THEN ASM_REWRITE_TAC[]
  THEN MP_TAC(ISPECL[`x:real^3`;`v:real^3`;`w:real^3`;`w1:real^3`]azim) THEN STRIP_TAC THEN STRIP_TAC
  THEN SUBGOAL_THEN`azim (x:real^3) v w1 u <= azim x v w u` ASSUME_TAC
THENL(*6*)[ REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;(*6*)
POP_ASSUM MP_TAC THEN POP_ASSUM(fun th->REWRITE_TAC[]) THEN ASM_REWRITE_TAC[] THEN
MP_TAC (ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(w1:real^3)`]properties_of_set_of_edge)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC 
 THEN REMOVE_THEN "b" (fun th->MP_TAC (ISPEC`{(v:real^3),(w:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM (fun th->MP_TAC (ISPEC`{(v:real^3),(u:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM (fun th->MP_TAC (ISPEC`{(v:real^3),w1}`th) THEN ASSUME_TAC(th))
  THEN REWRITE_TAC[SET_RULE`{a} UNION {b,c}={a,b,c}`] THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC
THEN
  DISJ_CASES_TAC(REAL_ARITH `(azim (x:real^3)  (v:real^3) (u:real^3) (w1:real^3)= &0) \/ ~(azim (x:real^3)  (v:real^3) (u:real^3) (w1:real^3) = &0)`)
THENL(*7*)[
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`;`w1:real^3`]UNIQUE_AZIM_0_POINT_FAN) 
THEN SET_TAC[];(*7*)

  DISJ_CASES_TAC(REAL_ARITH `(azim (x:real^3)  (v:real^3) (u:real^3) (w:real^3)= &0) \/ ~(azim (x:real^3)  (v:real^3) (u:real^3) (w:real^3) = &0)`)
THENL(*8*)[
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`;`w:real^3`]UNIQUE_AZIM_0_POINT_FAN) 
THEN SET_TAC[];(*8*)
 MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (u:real^3)`;` (w1:real^3)`]AZIM_COMPL) THEN ASM_REWRITE_TAC[]
   THEN  MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (u:real^3)`;` (w:real^3)`]AZIM_COMPL) THEN ASM_REWRITE_TAC[]
   THEN DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
   THEN FIND_ASSUM(MP_TAC o (SPEC`w1:real^3`))`!w1:real^3.  w1 IN set_of_edge v V E /\ ~(w1 = u)
           ==> &2 * pi - azim x v u w <= &2 * pi - azim x v u w1` 
 THEN REMOVE_THEN "be" MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN ASM_REWRITE_TAC[] THEN DISJ_CASES_TAC(SET_RULE`~(w1:real^3=u)\/ (w1=u)`)
THENL(*9*)[
ASM_REWRITE_TAC[REAL_ARITH`&2 * pi -(a:real)<= &2 *pi - b <=> b <= a`] THEN DISJ_CASES_TAC(SET_RULE `(azim(x:real^3) v u w =azim x v u w1)\/ ~(azim(x:real^3) v u w =azim x v u w1)`) 
THENL(*10*)[
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`;` (w:real^3)`;`(w1:real^3)`]UNIQUE_AZIM_POINT_FAN) THEN ASM_REWRITE_TAC[];(*10*)
POP_ASSUM MP_TAC THEN REAL_ARITH_TAC](*10*);(*9*)
SUBGOAL_THEN `azim (x:real^3) v w u= azim x v w w1` ASSUME_TAC
THENL(*10*)[POP_ASSUM(fun th->REWRITE_TAC[th]);(*10*)
REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC](*10*)(*9*)](*8*)](*7*)](*6*)](*5*)](*4*)](*3*);
SET_TAC[]]]]);;






let MONO_SIGMA_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (w:real^3).
FAN(x,V,E) /\ ({v,u} IN E)
/\ ({v,w} IN E)/\
 (sigma_fan x V E v u= sigma_fan x V E v w)
==> u=w
`,
REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC"1") 
THEN USE_THEN "1" MP_TAC THEN REWRITE_TAC[FAN;fan6] 
THEN REPEAT STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC"1") THEN 
DISCH_THEN (LABEL_TAC"a") THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN(LABEL_TAC "b") THEN
REPEAT STRIP_TAC THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (u:real^3)`;` (v:real^3)`]properties_of_graph) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN DISJ_CASES_TAC(SET_RULE`(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={(u:real^3)})\/ ~((set_of_edge v V E={u}))`)
THENL(*1*)[
POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[set_of_edge; EXTENSION;IN_ELIM_THM] 
THEN DISCH_TAC THEN POP_ASSUM(fun th-> MP_TAC(ISPEC`w:real^3`th)) THEN ASM_REWRITE_TAC[] 
THEN REMOVE_THEN "a" MP_TAC THEN REWRITE_TAC[UNIONS;SUBSET; IN_ELIM_THM]
THEN DISCH_TAC THEN POP_ASSUM (fun th->MP_TAC(ISPEC`w:real^3`th)) 
THEN ASM_REWRITE_TAC[IN_SING;LEFT_IMP_EXISTS_THM]
THEN STRIP_TAC THEN POP_ASSUM (fun th->MP_TAC(ISPEC`{(v:real^3),(w:real^3)}`th)) 
  THEN SET_TAC[];(*1*)

DISJ_CASES_TAC(SET_RULE`(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={(w:real^3)})\/ ~((set_of_edge v V E={w}))`)
THENL(*2*)[

POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[set_of_edge; EXTENSION;IN_ELIM_THM] 
THEN DISCH_TAC THEN POP_ASSUM(fun th-> MP_TAC(ISPEC`u:real^3`th)) THEN ASM_REWRITE_TAC[] 
THEN REMOVE_THEN "a" MP_TAC THEN REWRITE_TAC[UNIONS;SUBSET; IN_ELIM_THM]
THEN DISCH_TAC THEN POP_ASSUM (fun th->MP_TAC(ISPEC`u:real^3`th)) 
THEN ASM_REWRITE_TAC[IN_SING;LEFT_IMP_EXISTS_THM]
THEN STRIP_TAC THEN POP_ASSUM (fun th->MP_TAC(ISPEC`{(v:real^3),(u:real^3)}`th)) 
  THEN SET_TAC[];(*2*)


MP_TAC(ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (u:real^3)`]properties_of_set_of_edge)
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
MP_TAC(ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (w:real^3)`]properties_of_set_of_edge)
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]SIGMA_FAN)
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
  THEN POP_ASSUM(fun th-> MP_TAC(ISPEC`(w:real^3)`th))
THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (w:real^3)`]SIGMA_FAN)
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
  THEN POP_ASSUM(fun th-> MP_TAC(ISPEC`(u:real^3)`th))
  THEN ASM_REWRITE_TAC[] 
THEN MP_TAC (ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))`]properties_of_set_of_edge)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC 
 THEN REMOVE_THEN "b" (fun th->MP_TAC (ISPEC`{(v:real^3),(w:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM (fun th->MP_TAC (ISPEC`{(v:real^3),(u:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM (fun th->MP_TAC (ISPEC`{(v:real^3),(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3))}`th) THEN ASSUME_TAC(th))
  THEN REWRITE_TAC[SET_RULE`{a} UNION {b,c}={a,b,c}`] THEN ASM_REWRITE_TAC[] 
  THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
DISJ_CASES_TAC(SET_RULE`~((u:real^3)=(w:real^3))\/ u=w`)

THENL(*3*)[
ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `{(w:real^3),(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)),(u:real^3)}SUBSET set_of_edge v V E` ASSUME_TAC
THENL(*4*)[ SET_TAC[];(*4*)

MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`]CYCLIC_SET_EDGE_FAN) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;`{(w:real^3), (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)),(u:real^3)}`;`set_of_edge(v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)` ]subset_cyclic_set_fan)
		THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (w:real^3)`;`(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))`;` (u:real^3)`]sum2_azim_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "c") THEN
  DISJ_CASES_TAC(REAL_ARITH `(azim (x:real^3)  (v:real^3) (w:real^3) (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))= &0) \/ ~(azim (x:real^3)  (v:real^3) (w:real^3) (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)) = &0)`)

THENL(*5*)[
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (w:real^3)`;`(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))`]UNIQUE_AZIM_0_POINT_FAN) 
THEN SET_TAC[];(*5*)

DISJ_CASES_TAC(REAL_ARITH `(azim (x:real^3)  (v:real^3) (w:real^3) (u:real^3)= &0) \/ ~(azim (x:real^3)  (v:real^3) (w:real^3) (u:real^3) = &0)`)

THENL(*6*)[

MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (w:real^3)`;`(u:real^3)`]UNIQUE_AZIM_0_POINT_FAN) 
THEN SET_TAC[];(*6*)

  DISJ_CASES_TAC(REAL_ARITH `(azim (x:real^3)  (v:real^3)  (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)) (u:real^3)= &0) \/ ~(azim (x:real^3)  (v:real^3) (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)) (u:real^3) = &0)`)

THENL(*7*)[
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;`(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))`;` (u:real^3)`]UNIQUE_AZIM_0_POINT_FAN) 
THEN SET_TAC[];(*7*)

MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;`(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))`;` (u:real^3)`]AZIM_COMPL) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (w:real^3)`;` (u:real^3)`]AZIM_COMPL) THEN 
ASM_REWRITE_TAC[REAL_ARITH`&2 * pi - ((a:real)+(b:real))= --(a:real)+ (&2 * pi - b)`] THEN DISCH_TAC 
THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_ARITH`b <= (a:real)+(b:real)<=> &0 <= a`]
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;`(w:real^3)`;`(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))`] azim)THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC
(*7*)](*6*)](*5*)](*4*)];(*3*)

ASM_REWRITE_TAC[](*3*)]]]);;




let permutes_sigma_fan=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3).
FAN(x,V,E) /\ ({v,u} IN E)
==>
(extension_sigma_fan x V E v) permutes (set_of_edge v V E)`,
REPEAT GEN_TAC THEN STRIP_TAC THEN FIND_ASSUM(MP_TAC)`FAN((x:real^3), V, E)` THEN REWRITE_TAC[FAN;fan1] THEN STRIP_TAC
THEN MP_TAC(ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`]remark_finite_fan1)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)`;`extension_sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3)`]PERMUTES_FINITE_INJECTIVE)
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THENL[
GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[extension_sigma_fan];
STRIP_TAC
THENL[
GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[extension_sigma_fan] THEN DISJ_CASES_TAC(SET_RULE`set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={(x':real^3)}\/ ~(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={(x':real^3)})`)
THENL[ASM_REWRITE_TAC[sigma_fan;IN_SING];
ASM_MESON_TAC[SIGMA_FAN]];
REPEAT GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[extension_sigma_fan] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (x':real^3)`]properties_of_set_of_edge)
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
MP_TAC(ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (y:real^3)`]properties_of_set_of_edge)
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
ASM_MESON_TAC[MONO_SIGMA_FAN]]]);;


let CARD_SIGMA_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3).
FAN(x,V,E) ==> 
CARD( IMAGE (sigma_fan x V E v) (set_of_edge v V E))= CARD(set_of_edge v V E)
`,

REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN STRIP_TAC
THENL[
REPEAT GEN_TAC THEN STRIP_TAC THEN
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;`x':real^3`]properties_of_set_of_edge_fan)
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;`y:real^3`]properties_of_set_of_edge_fan)
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
ASM_MESON_TAC[MONO_SIGMA_FAN];
POP_ASSUM MP_TAC THEN REWRITE_TAC[FAN;fan1] THEN MESON_TAC[remark_finite_fan1]]);;



let MONO_AZIM_SIGMA_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (w:real^3).
FAN(x,V,E) /\ ({v,u} IN E)
/\ ({v,w} IN E) /\ ~(sigma_fan x V E v w =u)
==> (azim x v u w <= azim x v u (sigma_fan x V E v w))`,

REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC"1") 
THEN USE_THEN "1" MP_TAC THEN REWRITE_TAC[FAN;fan6] 
THEN REPEAT STRIP_TAC
THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC"1") THEN 
DISCH_THEN (LABEL_TAC"a") THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN(LABEL_TAC "b")
  THEN REPEAT STRIP_TAC THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (u:real^3)`;` (v:real^3)`]properties_of_graph) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN DISJ_CASES_TAC(SET_RULE`({(w:real^3)}=set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) \/ ~({(w:real^3)}=set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))`)
THENL(*1*)[
ASM_REWRITE_TAC[sigma_fan] THEN REAL_ARITH_TAC;(*1*)

DISJ_CASES_TAC(SET_RULE`((u:real^3)=(w:real^3))\/ ~(u=w)`)
THENL (*2*)[

ASM_REWRITE_TAC[AZIM_REFL] THEN MESON_TAC[azim];(*2*)

DISJ_CASES_TAC(SET_RULE`(azim (x:real^3) (v:real^3) (u:real^3) (w:real^3) <= azim (x:real^3) (v:real^3) (u:real^3) (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)) ) \/ ~(azim (x:real^3) (v:real^3) (u:real^3) (w:real^3) <= azim (x:real^3) (v:real^3) (u:real^3) (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)) )`)
  THENL (*3*)[
ASM_REWRITE_TAC[];(*3*)

SUBGOAL_THEN`azim (x:real^3) (v:real^3) (u:real^3) (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)) 
<= azim (x:real^3) (v:real^3) (u:real^3) (w:real^3) ` ASSUME_TAC
THENL(*4*)[
POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;(*4*)

MP_TAC(ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (u:real^3)`]properties_of_set_of_edge)
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
MP_TAC(ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (w:real^3)`]properties_of_set_of_edge)
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (w:real^3)`]SIGMA_FAN)
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
  THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "c") THEN 
 SUBGOAL_THEN `{(u:real^3),(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)),(w:real^3)}SUBSET set_of_edge v V E` ASSUME_TAC
THENL(*5*)[
SET_TAC[];(*5*)

MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`]CYCLIC_SET_EDGE_FAN) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;`{(u:real^3), (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)),(w:real^3)}`;`set_of_edge(v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)` ]subset_cyclic_set_fan)
		THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (u:real^3)`;`(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))`;` (w:real^3)`]sum2_azim_fan) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THEN  SUBGOAL_THEN `azim (x:real^3) (v:real^3) (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)) (w:real^3)<= azim x v u w` ASSUME_TAC

THENL(*6*)[
MP_TAC(ISPECL[`x:real^3`; `v:real^3`; `u:real^3`; `sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)`]azim) THEN REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;(*6*)

POP_ASSUM MP_TAC THEN POP_ASSUM (fun th-> REWRITE_TAC[])THEN  ASM_REWRITE_TAC[] THEN
MP_TAC (ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))`]properties_of_set_of_edge)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
 THEN REMOVE_THEN "b" (fun th->MP_TAC (ISPEC`{(v:real^3),(w:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM (fun th->MP_TAC (ISPEC`{(v:real^3),(u:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM (fun th->MP_TAC (ISPEC`{(v:real^3),(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))}`th) THEN ASSUME_TAC(th))
  THEN REWRITE_TAC[SET_RULE`{a} UNION {b,c}={a,b,c}`]
THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[]
  THEN 
  DISJ_CASES_TAC(REAL_ARITH `(azim (x:real^3)  (v:real^3) (w:real^3) (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))= &0) \/ ~(azim (x:real^3)  (v:real^3) (w:real^3) (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)) = &0)`)
THENL(*7*)[
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (w:real^3)`;`(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))`]UNIQUE_AZIM_0_POINT_FAN) 
THEN SET_TAC[];(*7*)

DISJ_CASES_TAC(REAL_ARITH `(azim (x:real^3)  (v:real^3) (w:real^3) (u:real^3)= &0) \/ ~(azim (x:real^3)  (v:real^3) (w:real^3) (u:real^3) = &0)`)

THENL(*8*)[ 
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (w:real^3)`;`(u:real^3)`]UNIQUE_AZIM_0_POINT_FAN) 
THEN SET_TAC[];(*8*)

MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;`w:real^3`;`(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))`]AZIM_COMPL) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (w:real^3)`;` (u:real^3)`]AZIM_COMPL)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[REAL_ARITH`&2 * pi - a<= &2 * pi - (b:real) <=> b<= (a:real)`]
  THEN REMOVE_THEN "c" (fun th -> MP_TAC(ISPEC `u:real^3` th) ) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC
  THEN SUBGOAL_THEN `azim (x:real^3) (v:real^3) (w:real^3) (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)) = azim x v  w u` ASSUME_TAC

THENL(*9*)[
POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN  REAL_ARITH_TAC;(*9*)

MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (w:real^3)`;`(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))`;`u:real^3`]UNIQUE_AZIM_POINT_FAN) 
  THEN ASM_REWRITE_TAC[]]]]]]]]]]);;







let image_power_map_points=prove(`!(i:num) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) .
FAN(x,V,E)  /\ (u IN set_of_edge v V E)
==> power_map_points (sigma_fan) x V E v u i IN set_of_edge v V E`,
INDUCT_TAC THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[power_map_points]
THENL[
ASM_MESON_TAC[];
REPEAT (POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC "a") THEN REPEAT DISCH_TAC 
THEN REMOVE_THEN "a" (fun th -> MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool) `;`(E:(real^3->bool)->bool)`;` (v:real^3) `;`(u:real^3)`] th)) THEN
ASM_REWRITE_TAC[] THEN DISCH_TAC 
  THEN DISJ_CASES_TAC(SET_RULE `set_of_edge v V E ={power_map_points (sigma_fan) x V E v u i}\/ ~(set_of_edge v V E ={power_map_points (sigma_fan) x V E v u i})`)
THENL[ASM_MESON_TAC[sigma_fan];
ASM_MESON_TAC[SIGMA_FAN]]]);;



let MONO_POWER_SIGMA_FAN=prove(`!(i:num) (j:num) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3).
FAN(x,V,E) /\ ({v,u} IN E)/\(j<i)/\
 (power_map_points sigma_fan x V E v u i)= (power_map_points sigma_fan x V E v u j)
==> u=power_map_points sigma_fan x V E v u (i-j)`,
INDUCT_TAC THENL
[ARITH_TAC;

INDUCT_TAC THENL
[REWRITE_TAC[ARITH_RULE `SUC i- 0 =SUC (i:num)`;power_map_points] THEN SET_TAC[];

REWRITE_TAC[ARITH_RULE `SUC (i:num)-SUC (j:num)= i - j`; ARITH_RULE `SUC(j:num) < SUC (i) <=> j < i`;power_map_points]
  THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC "a") THEN DISCH_TAC
  THEN REPEAT GEN_TAC THEN STRIP_TAC THEN 
   MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`v:real^3`;` (u:real^3)`]properties_of_set_of_edge_fan)
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
  THEN MP_TAC(ISPECL[`(i:num)`;` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]image_power_map_points) THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(j:num)`;` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]image_power_map_points) THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC
  THEN  MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`v:real^3`;`power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)`]properties_of_set_of_edge_fan)
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
  THEN  MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`v:real^3`;`power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (j:num)`]properties_of_set_of_edge_fan)
  THEN ASM_REWRITE_TAC[] THEN STRIP_TAC 
  THEN MP_TAC(ISPECL[` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;`power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)`;`power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (j:num)`]MONO_SIGMA_FAN) THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC
  THEN REMOVE_THEN "a"(fun th-> MP_TAC(ISPECL[`(j:num) `;`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]th))
  THEN ASM_REWRITE_TAC[]]]);;






let MONO_POWER_MAP_POINTS1_FAN=prove(`!(i:num)  (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) .
FAN(x,V,E) /\ (u IN set_of_edge v V E) /\ ~(set_of_edge v V E={u})
==> ~(power_map_points (sigma_fan) x V E v u i=power_map_points (sigma_fan) x V E v u (SUC i))
`,
INDUCT_TAC THENL[
REWRITE_TAC[power_map_points] THEN REPEAT GEN_TAC THEN STRIP_TAC 
THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]SIGMA_FAN) THEN ASM_MESON_TAC[];
REPEAT GEN_TAC THEN POP_ASSUM  
 (fun th-> MP_TAC(ISPECL[`(x:real^3) `;`(V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]th))THEN REWRITE_TAC[power_map_points] 
  THEN STRIP_TAC THEN STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC)
THEN DISCH_THEN (LABEL_TAC "a") THEN DISCH_THEN (LABEL_TAC "b") 
THEN USE_THEN "b" MP_TAC THEN REWRITE_TAC[FAN]
THEN STRIP_TAC
THEN  DISCH_TAC THEN DISCH_TAC 
THEN REMOVE_THEN "a" MP_TAC THEN MP_TAC(ARITH_RULE `SUC (i:num)< CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))==> i < CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))`)
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] 
THEN MATCH_MP_TAC MONO_NOT THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(i:num)`;` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]image_power_map_points) THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC
THEN MP_TAC(ISPECL[`SUC (i:num)`;` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]image_power_map_points) THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC
  THEN MP_TAC(ISPECL[` (v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num))`] properties_of_set_of_edge) 
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC(ISPECL[` (v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (SUC (i:num)))`] properties_of_set_of_edge) 
  THEN ASM_REWRITE_TAC[power_map_points] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`v:real^3`;`power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)`;`sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num))`]MONO_SIGMA_FAN) 
THEN ASM_MESON_TAC[]]);;








let MONO_AZIM_POWER_SIGMA_FAN=prove(`!  (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num).
FAN(x,V,E) /\ ({v,u} IN E) /\ ~(power_map_points (sigma_fan) x V E v u (SUC i) = u)
==> azim x v u (power_map_points (sigma_fan) x V E v u i)<= azim x v u (power_map_points (sigma_fan) x V E v u (SUC i))
`,
REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC"1") 
THEN USE_THEN "1" MP_TAC THEN REWRITE_TAC[FAN;fan6; power_map_points] 
THEN REPEAT STRIP_TAC
THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC"1") THEN REPEAT STRIP_TAC 
  THEN MP_TAC (ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (u:real^3)`]properties_of_set_of_edge)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC(ISPECL[`(i:num)`;` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]image_power_map_points) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
THEN MP_TAC (ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`power_map_points (sigma_fan)(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)`]properties_of_set_of_edge)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
MP_TAC(ISPECL[`(x:real^3) `;`(V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`;`power_map_points (sigma_fan)(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)`]MONO_AZIM_SIGMA_FAN) THEN ASM_REWRITE_TAC[]);;









(* Proof of Lemma [VBTIKLP] *)


let lemma62=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 w:real^3 w1:real^3. 
a IN a_node_fan x V E (x,v,w,w1)==>(?n. a=(x,v,(power_map_points sigma_fan x V E v w n),(power_map_points sigma_fan x V E v w (SUC n))))`, 
REWRITE_TAC[a_node_fan; IN_ELIM_THM; ] THEN REWRITE_TAC[node_fan] THEN REWRITE_TAC[power_n_fan]);;


let complement_set= new_definition`complement_set {x:real^3, v:real^3} = {y:real^3| ~(y IN aff {x,v})} `;;

let subset_aff=prove(`!x:real^3 v:real^3. (aff{x, v} SUBSET (UNIV:real^3->bool))`, REPEAT GEN_TAC THEN SET_TAC[]);;


let union_aff=prove(`!x v:real^3. (UNIV:real^3->bool) = aff{x, v} UNION  complement_set {x, v}  `,
REPEAT GEN_TAC  THEN REWRITE_TAC[complement_set] THEN SET_TAC[]);;

(*---------------------------------------------------------------*)
(* the properties of if_azims_fan                                *)
(*---------------------------------------------------------------*)





let if_azims_fan= new_definition`
if_azims_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)
    = if i = CARD(set_of_edge v V E) 
        then &2 * pi 
         else azim x v u (power_map_points sigma_fan x V E v u i)`;;

let if_azims_works_fan=prove(
`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num).
( &0 <= if_azims_fan x V E v u i) /\  if_azims_fan x V E v u i <= &2 * pi`,
REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ARITH `(a:real) <= (b:real) <=> (b >= a)`; if_azims_fan; azim;COND_ELIM_THM] 
  THEN MP_TAC(ISPECL [`x:real^3`; `v:real^3`; `u:real^3`;
`power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)`]azim)
  THEN STRIP_TAC 
  THEN ASSUME_TAC(PI_WORKS) THEN ASM_REWRITE_TAC[]
  THEN REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;




let set_of_orbits_points_fan = new_definition `set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) = {power_map_points sigma_fan x V E v u i| 0<=i }`;;

let number_of_orbits_fan = new_definition `number_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) = CARD(set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3))`;;



let addition_sigma_fan = prove(`!(m:num) (n:num) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3). 
power_map_points sigma_fan x V E v u (m + n) = (power_map_points sigma_fan x V E v (power_map_points sigma_fan x V E v u  n) m)  `,
INDUCT_TAC 
THENL [
REWRITE_TAC[power_map_points; ARITH_RULE`0 + n:num =n`];
REWRITE_TAC[ARITH_RULE` SUC (m:num) + n= SUC(m+n)`; power_map_points] THEN REPEAT GEN_TAC
  THEN POP_ASSUM(ASSUME_TAC o GSYM o (ISPECL[`(n:num) `;`(x:real^3) `;`(V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]))
		   THEN SET_TAC[]]);;






let fix_point_sigma_fan=prove(`! (q:num) (i:num) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3).
(power_map_points (sigma_fan) x V E v u i=u) 
==>power_map_points sigma_fan x V E v u (q * i)=u
`,
INDUCT_TAC THENL[
ASM_REWRITE_TAC[ARITH_RULE`0 * i:num = 0`;power_map_points];
REWRITE_TAC[ARITH_RULE`SUC q * i:num= q * i + i`] THEN REPEAT GEN_TAC THEN
 POP_ASSUM(MP_TAC  o (ISPECL[`(i:num) `;`(x:real^3) `;`(V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]))
  THEN DISCH_THEN(LABEL_TAC "a") THEN DISCH_TAC THEN REMOVE_THEN "a" MP_TAC THEN ASM_REWRITE_TAC[addition_sigma_fan]]);;

let u_IN_ORBITS_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) .
 u IN set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)`,
REWRITE_TAC[set_of_orbits_points_fan; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN EXISTS_TAC`0` THEN REWRITE_TAC[power_map_points] THEN SIMP_TAC[] THEN ARITH_TAC);;



let IN_ORBITS_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (w:real^3).
 w IN set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)
==> sigma_fan x V E v w IN set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)`,

REPEAT GEN_TAC THEN REWRITE_TAC[set_of_orbits_points_fan; IN_ELIM_THM] THEN STRIP_TAC THEN EXISTS_TAC`SUC i` THEN ASM_REWRITE_TAC[power_map_points] THEN ARITH_TAC);;


let ORBITS_SUBSET_EDGE_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) .
FAN(x,V,E) /\ ({v,u} IN E)
==> set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) 
SUBSET set_of_edge v V E`,
REPEAT GEN_TAC THEN STRIP_TAC
  THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`v:real^3`;` (u:real^3)`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[set_of_orbits_points_fan;SUBSET; IN_ELIM_THM] THEN DISCH_TAC THEN GEN_TAC THEN STRIP_TAC
THEN MP_TAC(ISPECL[`(i:num)`;` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]image_power_map_points) THEN ASM_REWRITE_TAC[]);;


let CARD_ORBITS_EDGE_FAN_LE=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) .
FAN(x,V,E) /\ ({v,u} IN E)
==> CARD(set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) )
<=CARD( set_of_edge v V E)`,
REPEAT GEN_TAC THEN STRIP_TAC
  THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`v:real^3`;` (u:real^3)`]ORBITS_SUBSET_EDGE_FAN)
  THEN ASM_REWRITE_TAC[] THEN REPEAT (POP_ASSUM MP_TAC)
THEN REWRITE_TAC[FAN;fan1] THEN REPEAT STRIP_TAC
  THEN MP_TAC(ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`] remark_finite_fan1)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC(ISPECL[`set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)`;`set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)`]CARD_SUBSET)
  THEN ASM_REWRITE_TAC[]);;




let FINITE_ORBITS_SIGMA_FAN=prove( `!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) .
FAN(x,V,E) /\ ({v,u} IN E)
==> FINITE(set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)) `,

REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`v:real^3`;` (u:real^3)`] ORBITS_SUBSET_EDGE_FAN)THEN ASM_REWRITE_TAC[] 
  THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[FAN;fan1] THEN STRIP_TAC
  THEN MP_TAC(ISPECL[`(v:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`] remark_finite_fan1)
  THEN ASM_REWRITE_TAC[] THEN MESON_TAC[FINITE_SUBSET]);;



let ORBITS_SIGMA_FAN=prove(`!(i:num) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) .
FAN(x,V,E) /\ ({v,u} IN E)/\
(power_map_points (sigma_fan) x V E v u i=u) /\ ~(i=0)
==> set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) =
{power_map_points sigma_fan x V E v u j| j < i }
`,
REPEAT STRIP_TAC THEN REWRITE_TAC[set_of_orbits_points_fan; EXTENSION; IN_ELIM_THM]
THEN GEN_TAC THEN EQ_TAC
THENL [
STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
FIND_ASSUM (MP_TAC o (SPEC `i':num`) o MATCH_MP DIVMOD_EXIST) `~(i:num = 0)`
 THEN REPEAT STRIP_TAC
  THEN EXISTS_TAC`r:num` THEN ASM_REWRITE_TAC[ARITH_RULE`q * (i:num) + r = r+ q * i`;addition_sigma_fan]
  THEN MP_TAC  (SPECL [`(q:num)`;` (i:num)`;` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3) `;`(u:real^3)`]fix_point_sigma_fan) THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC THEN ASM_REWRITE_TAC[];

STRIP_TAC THEN EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

 


let CARD_ORBITS_SIGMA_FAN_LE=prove(`!(i:num) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) .
FAN(x,V,E) /\ ({v,u} IN E)/\
(power_map_points (sigma_fan) x V E v u i=u) /\ ~(i=0)
==> CARD(set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3))<=i`,

REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC(ISPECL[`(i:num)`;` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]ORBITS_SIGMA_FAN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
THEN MP_TAC(ISPECL[`i:num`;`power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)`]CARD_FINITE_SERIES_LE) THEN SET_TAC[]);;




let exists_inverse_in_orbits_sigma_fan=prove(`
!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (y:real^3).
~ (set_of_edge v V E= {u} ) 
/\ FAN(x,V,E) /\ (y IN (set_of_edge v V E))/\({v,u} IN E)/\ ~(y IN set_of_orbits_points_fan x V E v u) 
==>
(?(w:real^3). (w IN (set_of_orbits_points_fan x V E v u)) /\ ~(w=y) /\
(!(w1:real^3). (w1 IN (set_of_orbits_points_fan x V E v u))/\ ~(w1=y) ==> azim1 x v y w <=  azim1 x v y w1))
`,

(let lemma = prove
   (`!X:real->bool. 
          FINITE X /\ ~(X = {}) 
          ==> ?a. a IN X /\ !x. x IN X ==> a <= x`,
    MESON_TAC[INF_FINITE]) in

MP_TAC(lemma) THEN DISCH_THEN(LABEL_TAC "a") THEN REPEAT GEN_TAC
THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC "ba") 
THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` (u:real^3)`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`v:real^3`;` (u:real^3)`]FINITE_ORBITS_SIGMA_FAN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
THEN
SUBGOAL_THEN `FINITE ((set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) (v:real^3) (u:real^3) DELETE  (y:real^3))` ASSUME_TAC
THENL[(*1*)

ASM_MESON_TAC[FINITE_DELETE_IMP];(*1*)
DISJ_CASES_TAC(SET_RULE`(set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) DELETE  (y:real^3)={})\/
 ~(set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) DELETE  (y:real^3)={})`)
THENL(*2*)[
MP_TAC (ISPECL[`y:real^3`;`set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)`]DELETE_NON_ELEMENT) 
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`v:real^3`;` (u:real^3)`]u_IN_ORBITS_FAN)
  THEN SET_TAC[];(*2*)
SUBGOAL_THEN`~(IMAGE ( azim1 x v y) (set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) DELETE  (y:real^3))={})` ASSUME_TAC
THENL(*3*)[
REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM_MESON_TAC[];(*3*)

SUBGOAL_THEN` FINITE (IMAGE (azim1 x v y) (set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) DELETE  (y:real^3)))` ASSUME_TAC
THENL(*4*)[
ASM_MESON_TAC[FINITE_IMAGE];(*4*)

REMOVE_THEN "a" (fun th ->MP_TAC(ISPEC `(IMAGE (azim1 x v y) (set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) DELETE  (y:real^3)))` th))
 THEN ASM_REWRITE_TAC[IMAGE;DELETE;IN_ELIM_THM]THEN STRIP_TAC
THEN EXISTS_TAC`x':real^3`
  THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]]]]));;










let key_lemma_cyclic_fan=prove(`!(i:num) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3).
FAN(x,V,E) /\ (0 < i) /\(i< CARD(set_of_edge v V E)) /\ ({v,u} IN E)
==> ~(power_map_points (sigma_fan) x V E v u i=u)
`,
INDUCT_TAC
THENL(*1*)[ARITH_TAC;(*1*)
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[power_map_points] THEN
MP_TAC(ISPECL[` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]ORBITS_SUBSET_EDGE_FAN) 
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN DISJ_CASES_TAC(SET_RULE`(sigma_fan x V E v (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num))= u)\/ ~(sigma_fan x V E v (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num))= u)`)
THENL(*2*)[
ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL[`SUC (i:num)`;` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]CARD_ORBITS_SIGMA_FAN_LE)
 THEN ASM_REWRITE_TAC[power_map_points; ARITH_RULE`~(SUC i = 0)`] THEN STRIP_TAC
  THEN SUBGOAL_THEN `CARD(set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)) <CARD(set_of_edge v V E)` ASSUME_TAC
THENL(*3*)[
REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC;(*3*)

SUBGOAL_THEN `set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) PSUBSET set_of_edge v V E` ASSUME_TAC
THENL(*4*)[
ASM_REWRITE_TAC[PSUBSET] THEN DISJ_CASES_TAC(SET_RULE`(set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) = set_of_edge v V E)\/ ~(set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) = set_of_edge v V E)`)
THENL(*5*)[
SUBGOAL_THEN`CARD(set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)) =CARD( set_of_edge v V E)`ASSUME_TAC
THENL(*6*)[
POP_ASSUM(fun th->REWRITE_TAC[th]);(*6*)
POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC](*6*);(*5*)

POP_ASSUM(fun th->REWRITE_TAC[th])](*5*);(*4*)


POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[PSUBSET_MEMBER] THEN STRIP_TAC
  THEN MP_TAC(ISPECL[` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`;`y:real^3`]
exists_inverse_in_orbits_sigma_fan)
  THEN ASM_REWRITE_TAC[] THEN DISJ_CASES_TAC(SET_RULE`(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={(u:real^3)})\/ ~(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={(u:real^3)})`)
THENL(*5*)[
POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC"a") 
  THEN DISCH_THEN(LABEL_TAC "b") THEN DISCH_TAC THEN REMOVE_THEN "a" MP_TAC THEN ASM_REWRITE_TAC[IN_SING] THEN DISCH_TAC
  THEN REMOVE_THEN "b" MP_TAC THEN ASM_REWRITE_TAC[u_IN_ORBITS_FAN];(*5*)

ASM_REWRITE_TAC[] THEN STRIP_TAC
THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
DISJ_CASES_TAC(SET_RULE`(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={(w:real^3)})\/ ~(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)={(w:real^3)})`)
THENL(*6*)[

POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC"a") 
  THEN DISCH_THEN(LABEL_TAC "b") THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN REMOVE_THEN "a" MP_TAC THEN ASM_REWRITE_TAC[IN_SING] THEN DISCH_TAC
  THEN REMOVE_THEN "b" MP_TAC THEN ASM_REWRITE_TAC[];(*6*)

MP_TAC(ISPECL[` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;`u:real^3`;` (w:real^3)`]IN_ORBITS_FAN)
  THEN ASM_REWRITE_TAC[]
  THEN STRIP_TAC THEN STRIP_TAC
THEN POP_ASSUM(fun th->MP_TAC(ISPEC `sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)` th))
  THEN ASM_REWRITE_TAC[]  
  THEN DISJ_CASES_TAC(SET_RULE`sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)=(y:real^3) \/ ~(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)=(y:real^3))`)
THENL(*7*)[
POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC"a") THEN DISCH_TAC THEN REMOVE_THEN "a" MP_TAC
  THEN ASM_REWRITE_TAC[];(*7*)

ASM_REWRITE_TAC[azim1;REAL_ARITH` (a:real) - b <= a - c <=> c<=b`] THEN STRIP_TAC
THEN
SUBGOAL_THEN `sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3) IN set_of_edge v V E` ASSUME_TAC
THENL(*8*)[
SET_TAC[];(*8*)

SUBGOAL_THEN `(w:real^3) IN set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)` ASSUME_TAC
THENL(*9*)[
SET_TAC[];(*9*)

SUBGOAL_THEN `{(y:real^3),sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3),(w:real^3)} SUBSET set_of_edge v V E` ASSUME_TAC

THENL(*10*)[
SET_TAC[];(*10*)

FIND_ASSUM(MP_TAC)`FAN((x:real^3),V,E)` THEN REWRITE_TAC[FAN;fan6] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "b") THEN STRIP_TAC THEN
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (u:real^3)`;` (v:real^3)`]properties_of_graph) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`]CYCLIC_SET_EDGE_FAN)
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;`{(y:real^3),sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3),(w:real^3)}`;`set_of_edge(v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)` ]subset_cyclic_set_fan)
		THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC(ISPECL[`x:real^3`;`v:real^3`;`y:real^3`;`sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)`;`w:real^3`]sum2_azim_fan) THEN ASM_REWRITE_TAC[]
  THEN MP_TAC(ISPECL[`x:real^3`;`v:real^3`;`y:real^3`;`sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)`]azim) 
THEN STRIP_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `azim (x:real^3) (v:real^3) (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)) (w:real^3) <= azim (x:real^3) (v:real^3) (y:real^3) (w:real^3)`
ASSUME_TAC
THENL(*11*)[
REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;(*11*)

POP_ASSUM MP_TAC THEN POP_ASSUM(fun th ->REWRITE_TAC[]) THEN ASM_REWRITE_TAC[]  THEN
MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` (y:real^3)`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` (w:real^3)`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
DISJ_CASES_TAC(REAL_ARITH `(azim (x:real^3)  (v:real^3) (w:real^3) (y:real^3)= &0) \/ ~(azim (x:real^3)  (v:real^3) (w:real^3) (y:real^3) = &0)`)
THENL(*12*)[
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (w:real^3)`;`(y:real^3)`]UNIQUE_AZIM_0_POINT_FAN)
THEN ASM_REWRITE_TAC[];(*12*)

DISJ_CASES_TAC(REAL_ARITH `(azim (x:real^3)  (v:real^3) (w:real^3) (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))= &0) \/ ~(azim (x:real^3)  (v:real^3) (w:real^3) (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3)) = &0)`)
THENL(*13*)[
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (w:real^3)`; ` (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))` ]UNIQUE_AZIM_0_POINT_FAN)
  THEN ASM_REWRITE_TAC[]
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (w:real^3)`] SIGMA_FAN)
  THEN ASM_REWRITE_TAC[] THEN SET_TAC[];(*13*)

 REMOVE_THEN "b" (fun th->MP_TAC (ISPEC`{(v:real^3),(w:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM (fun th->MP_TAC (ISPEC`{(v:real^3),(y:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM (fun th->MP_TAC (ISPEC`{(v:real^3),(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))}`th) THEN ASSUME_TAC(th))
  THEN REWRITE_TAC[SET_RULE`{(a:real^3)} UNION {b,c}={a,b,c}`] THEN ASM_REWRITE_TAC[] 
  THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;`(w:real^3)`;`(sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))`]AZIM_COMPL) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (w:real^3)`;` (y:real^3)`]AZIM_COMPL) THEN 
ASM_REWRITE_TAC[] THEN  DISCH_TAC 
THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ARITH`(a - (b:real) <= (a:real)- (c:real))<=> c <= b`]
   THEN STRIP_TAC
 THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;`(E:(real^3->bool)->bool)`;`v:real^3`; `(w:real^3)`] SIGMA_FAN)
   THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN POP_ASSUM(fun th-> MP_TAC(ISPEC`(y:real^3)`th))
   THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
   THEN SUBGOAL_THEN`azim (x:real^3) (v:real^3) (w:real^3) (y:real^3) = azim x v w (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))` ASSUME_TAC
THENL(*14*)[
POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC  THEN REAL_ARITH_TAC;(*14*)

MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;`(w:real^3)`;` (y:real^3)`; ` (sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (w:real^3))` ]UNIQUE_AZIM_POINT_FAN)
  THEN ASM_REWRITE_TAC[]

]]]]]]]]]]]];
ASM_REWRITE_TAC[]]]);;





let cyclic_power_sigma_fan=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) (j:num).
FAN(x,V,E) /\ (i< CARD(set_of_edge v V E))  /\ (j<i) /\ ({v,u} IN E)
==> ~(power_map_points (sigma_fan) x V E v u i= power_map_points (sigma_fan) x V E v u j)
`,

REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN 
MP_TAC(ISPECL[`(i:num)`;` (j:num)`;` (x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]MONO_POWER_SIGMA_FAN)
  THEN ASM_REWRITE_TAC[] THEN MP_TAC(ARITH_RULE` j < i ==> 0 < (i:num)-(j:num)`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ARITH_RULE` (j:num) <(i:num)==> i-j <= i`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ARITH_RULE` (i :num )-(j:num) <= i /\ i< CARD(set_of_edge (v:real^3)(V:real^3->bool) (E:(real^3->bool)->bool))==> i-j <CARD(set_of_edge (v:real^3)(V:real^3->bool) (E:(real^3->bool)->bool))`)  THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(i:num)-(j:num)`;` (x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]key_lemma_cyclic_fan)
  THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]);;





let CARD_SET_OF_ORBITS_POINTS_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3).
FAN(x,V,E) /\ ({v,u} IN E)
==> CARD(set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3))= CARD(set_of_edge v V E)`,

REPEAT GEN_TAC THEN STRIP_TAC THEN 
SUBGOAL_THEN`{power_map_points (sigma_fan) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) |i|   (i< CARD(set_of_edge v V E))}
SUBSET  set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)
`ASSUME_TAC
THENL[ REWRITE_TAC[set_of_orbits_points_fan;SUBSET;IN_ELIM_THM]
 THEN GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC`i:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;

SUBGOAL_THEN`CARD {power_map_points (sigma_fan) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) |i|   (i< CARD(set_of_edge v V E))}
<= CARD  (set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3))`
ASSUME_TAC
THENL[
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`] FINITE_ORBITS_SIGMA_FAN) THEN ASM_REWRITE_TAC[]
  THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`{power_map_points (sigma_fan) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) |i|   (i< CARD(set_of_edge v V E))}`;`set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)`]CARD_SUBSET) THEN ASM_REWRITE_TAC[];

MP_TAC(SPECL[`(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]cyclic_power_sigma_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`CARD(set_of_edge  (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))`;`power_map_points (sigma_fan) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)`]CARD_FINITE_SERIES_EQ)
		THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]CARD_ORBITS_EDGE_FAN_LE)
  THEN ASM_REWRITE_TAC[] THEN REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC]]);;


let SIMP_ORBITS_POINTS_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3).
FAN(x,V,E) /\ ({v,u} IN E)
==>
{power_map_points (sigma_fan) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) |i|   (i< CARD(set_of_edge v V E))}
= set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)
`,

REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN`{power_map_points (sigma_fan) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) |i|   (i< CARD(set_of_edge v V E))}
SUBSET  set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)
`ASSUME_TAC
THENL[
 REWRITE_TAC[set_of_orbits_points_fan;SUBSET;IN_ELIM_THM]
 THEN GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC`i:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;

POP_ASSUM MP_TAC THEN MP_TAC(SPECL[`(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]cyclic_power_sigma_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`CARD(set_of_edge  (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))`;`power_map_points (sigma_fan) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)`]CARD_FINITE_SERIES_EQ)
		THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC"a")
  THEN MP_TAC(SPECL[`(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]CARD_SET_OF_ORBITS_POINTS_FAN) THEN ASM_REWRITE_TAC[SET_RULE`a=b<=> b=a`] THEN DISCH_TAC THEN REMOVE_THEN "a" MP_TAC THEN ASM_REWRITE_TAC[] 
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`] FINITE_ORBITS_SIGMA_FAN) THEN ASM_REWRITE_TAC[]
  THEN MESON_TAC[CARD_SUBSET_EQ]]);;

let ORDER_POWER_SIGMA_FAN=prove(`!(i:num) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) .
FAN(x,V,E) /\ (i=CARD(set_of_edge v V E)) /\ ({v,u} IN E)
==> power_map_points (sigma_fan) x V E v u i= u
`,
REPEAT GEN_TAC THEN STRIP_TAC THEN SUBGOAL_THEN `power_map_points (sigma_fan) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) IN  set_of_orbits_points_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)` ASSUME_TAC
THENL[
 REWRITE_TAC[ set_of_orbits_points_fan; IN_ELIM_THM] THEN EXISTS_TAC`i:num` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;

POP_ASSUM MP_TAC THEN  MP_TAC(SPECL[`(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]SIMP_ORBITS_POINTS_FAN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN POP_ASSUM(fun th->REWRITE_TAC[SYM(th);]) THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC
		THEN ASM_REWRITE_TAC[] THEN
MP_TAC(ISPECL[`CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))`;`i':num`;`(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]MONO_POWER_SIGMA_FAN) THEN ASM_REWRITE_TAC[]
  THEN DISJ_CASES_TAC(ARITH_RULE`(0<(i':num))\/  i'=0`)
THENL[
DISCH_TAC THEN
MP_TAC(ARITH_RULE`0 < (i':num)/\ i'< CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) ==> (CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))- (i':num) < CARD (set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)))`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
  THEN MP_TAC(ARITH_RULE`(i':num)< CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))==> 0< CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))-i'`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
		THEN 
MP_TAC(ISPECL[`CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))-(i':num)`; `(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]key_lemma_cyclic_fan)
  THEN ASM_REWRITE_TAC[] THEN SET_TAC[];

ASM_REWRITE_TAC[power_map_points]]]);;







let SUM_IF_AZIMS_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num).
FAN(x,V,E) /\ ({v,u} IN E)
/\(0<i)
/\   (i< CARD(set_of_edge v V E)) 
==>
 if_azims_fan x V E v u (SUC i)= if_azims_fan x V E v u i + azim x v ((power_map_points sigma_fan x V E v u i)) (power_map_points sigma_fan x V E v u (SUC i))`,
REPEAT GEN_TAC THEN STRIP_TAC 
THEN REPEAT (POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC"a") THEN USE_THEN "a" MP_TAC 
  THEN REWRITE_TAC[FAN;fan6] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "b") 
  THEN REPEAT STRIP_TAC
THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` (u:real^3)`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
MP_TAC(ISPECL[`(i:num)`; `(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`] image_power_map_points) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
MP_TAC(ISPECL[`SUC(i:num)`; `(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`] image_power_map_points) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (SUC(i:num))`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
   THEN SUBGOAL_THEN `~((i:num)=CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)))` ASSUME_TAC
THENL(*1*)[
REPEAT(POP_ASSUM MP_TAC) THEN ARITH_TAC;(*1*)

DISJ_CASES_TAC(ARITH_RULE ` SUC (i:num)= CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) \/ ~(SUC i=CARD(set_of_edge v V E))`)
THENL(*2*)[

MP_TAC(ISPECL[`SUC (i:num)`; `(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]ORDER_POWER_SIGMA_FAN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
REWRITE_TAC[if_azims_fan] THEN ASM_REWRITE_TAC[] THEN POP_ASSUM (fun th-> REWRITE_TAC[SYM(th)] THEN ASSUME_TAC(th))
  THEN  REMOVE_THEN "b" (fun th->MP_TAC (ISPEC`{(v:real^3),(u:real^3)}`th) THEN ASSUME_TAC(th))
  THEN POP_ASSUM (fun th->MP_TAC (ISPEC`{(v:real^3),(power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num))}`th) THEN ASSUME_TAC(th))
  THEN REWRITE_TAC[SET_RULE`{(a:real^3)} UNION {b,c}={a,b,c}`] THEN ASM_REWRITE_TAC[] 
   THEN DISCH_TAC THEN DISCH_TAC THEN
DISJ_CASES_TAC(REAL_ARITH `(azim (x:real^3)  (v:real^3) (u:real^3) (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num))= &0) \/ ~(azim (x:real^3)  (v:real^3) (u:real^3) (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)) = &0)`)
THENL(*3*)[

MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`; ` (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num))` ]UNIQUE_AZIM_0_POINT_FAN)
  THEN ASM_REWRITE_TAC[]
  THEN  MP_TAC(ISPECL[`i:num`;`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`] key_lemma_cyclic_fan)
  THEN ASM_REWRITE_TAC[] THEN SET_TAC[];(*3*)

 MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;` (u:real^3)`;` (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num))`]AZIM_COMPL) THEN 
ASM_REWRITE_TAC[] THEN  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];(*2*)

ASM_REWRITE_TAC[if_azims_fan] THEN MP_TAC(ARITH_RULE`i:num < CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)) /\ ~(SUC(i) = CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)))==> SUC(i)<CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN ASSUME_TAC(ARITH_RULE`0<SUC(i:num)`)
  THEN MP_TAC(ISPECL[`SUC(i:num)`;`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`] key_lemma_cyclic_fan)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`;`i:num`]MONO_AZIM_POWER_SIGMA_FAN)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN SUBGOAL_THEN `{(u:real^3),power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num),power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (SUC(i:num))} SUBSET set_of_edge v V E` ASSUME_TAC
THENL(*3*)[
SET_TAC[];(*3*)

MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (u:real^3)`;` (v:real^3)`]properties_of_graph) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`]CYCLIC_SET_EDGE_FAN)
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;`{(u:real^3),power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num),power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (SUC(i:num))}`;`set_of_edge(v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)` ]subset_cyclic_set_fan)
		THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC(ISPECL[`x:real^3`;`v:real^3`;`u:real^3`;`power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)`;`power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (SUC(i:num))`]sum2_azim_fan) THEN ASM_REWRITE_TAC[]]]]);;

let azim_i_fan=new_definition`
azim_i_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)
= azim x v (power_map_points sigma_fan x V E v u i) (power_map_points sigma_fan x V E v u (SUC i))`;;


MP_TAC( ISPECL[`(SUC(0):num)`;` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3) `;`(u:real^3)`]ORDER_POWER_SIGMA_FAN) THEN ASM_REWRITE_TAC[power_map_points;ARITH_RULE`SUC 0=1`];;



let SUM_EQ_IF_AZIMS_FAN=prove(`!(i:num) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3).
FAN(x,V,E) /\ ({v,u} IN E)
/\ ~(set_of_edge v V E ={u})
/\ ~(1=CARD(set_of_edge v V E ))
/\   (i< CARD(set_of_edge v V E)) 
==> 
sum (0..i) (azim_i_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3))
= if_azims_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (SUC i)`,
INDUCT_TAC
THENL[
REPEAT STRIP_TAC THEN
ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG;azim_i_fan;power_map_points;if_azims_fan; ARITH_RULE`SUC 0=1`];

POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "a") 
THEN REPEAT STRIP_TAC
THEN
ASSUME_TAC(ARITH_RULE`0<= SUC (i:num)`)THEN ASSUME_TAC(ARITH_RULE`0< SUC (i:num)`) THEN
MP_TAC(ARITH_RULE`SUC (i:num)<CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))==> i< CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))`) THEN
ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG]
   THEN REMOVE_THEN"a"(fun th-> MP_TAC(ISPECL[`(x:real^3) `;`(V:real^3->bool) `;`(E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]th))
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN ASM_REWRITE_TAC[]
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool) `;`(E:(real^3->bool)->bool) `;`(v:real^3) `;`(u:real^3)`;` (SUC(i:num))`]SUM_IF_AZIMS_FAN)
  THEN ASM_REWRITE_TAC[azim_i_fan] THEN REAL_ARITH_TAC]);;





let SUM_AZIMS_EQ_2PI_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3).
FAN(x,V,E) /\ ({v,u} IN E)
/\ ~(set_of_edge v V E ={u})
/\ (1<CARD(set_of_edge v V E ))
==> 
sum (0..(CARD(set_of_edge v V E )-1)) (azim_i_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3))
= &2 *pi`,
REPEAT STRIP_TAC THEN 
MP_TAC(ARITH_RULE`(1<CARD(set_of_edge v V E )) ==> CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))-1 < CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))`)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN 
MP_TAC(ARITH_RULE`(1<CARD(set_of_edge v V E )) ==> ~(1=CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)))`)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN 
MP_TAC(ARITH_RULE`(1<CARD(set_of_edge v V E )) ==> SUC(CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))-1)= CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))`)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
MP_TAC(ISPECL[`CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))-1`;` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]SUM_EQ_IF_AZIMS_FAN)
  THEN ASM_REWRITE_TAC[if_azims_fan]);;


let AZIM_LE_POWER_SIGMA_FAN=prove(`!(i:num) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (j:num).
FAN(x,V,E) /\ ({v,u} IN E)
/\ ~(set_of_edge v V E ={u})
/\ (j<i)
/\   (i< CARD(set_of_edge v V E)) 
==>
 azim x v u (power_map_points sigma_fan x V E v u j) < azim x v u (power_map_points sigma_fan x V E v u i)`,
INDUCT_TAC
THENL(*1*)[
ARITH_TAC;(*1*)
  
REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN DISCH_THEN(LABEL_TAC"1") THEN DISCH_THEN (LABEL_TAC"a") THEN USE_THEN "a" MP_TAC 
  THEN REWRITE_TAC[FAN;fan6] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "b") 
  THEN REPEAT STRIP_TAC
THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` (u:real^3)`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
MP_TAC(ISPECL[`(i:num)`; `(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`] image_power_map_points) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
MP_TAC(ISPECL[`SUC(i:num)`; `(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`] image_power_map_points) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (SUC(i:num))`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC


THEN ASSUME_TAC(ARITH_RULE`i< SUC(i:num)`) THEN ASSUME_TAC(ARITH_RULE`0< SUC(i:num)`) 
  THEN MP_TAC(ARITH_RULE`SUC(i)< CARD(set_of_edge(v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))==> i< CARD(set_of_edge(v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))`)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
    THEN  MP_TAC(ISPECL[`SUC(i:num)`;`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`] key_lemma_cyclic_fan)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
   THEN MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`;`i:num`]MONO_AZIM_POWER_SIGMA_FAN)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC

THEN DISJ_CASES_TAC(ARITH_RULE `(j:num)< (i:num) \/ (i <= j)`)
THENL[
REMOVE_THEN "1" (fun th-> MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`; `(j:num)`] th)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;

MP_TAC(ARITH_RULE`(j:num) < SUC(i:num) ==> j <= i`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ARITH_RULE` (j:num) <= (i:num) /\ i<= j==> j=i`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN  ASM_REWRITE_TAC[]
  THEN SUBGOAL_THEN`~(azim x v u (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) ((i:num))) = azim x v u (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (SUC(i:num))))` ASSUME_TAC
THENL[
STRIP_TAC THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;`u:real^3`;` power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)`;` power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (SUC(i:num))`]UNIQUE_AZIM_POINT_FAN)
THEN  ASM_REWRITE_TAC[]
  THEN MP_TAC(ISPECL[`(i:num)`;`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`]MONO_POWER_MAP_POINTS1_FAN)
  THEN ASM_REWRITE_TAC[];

REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC]]]);;




let SUM_AZIM_POWER_SIGMA_FAN=prove(`!(i:num) (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (j:num).
FAN(x,V,E) /\ ({v,u} IN E)
/\ ~(set_of_edge v V E ={u})
/\ (j<i)
/\   (i< CARD(set_of_edge v V E)) 
==>
 azim x v u (power_map_points sigma_fan x V E v u i)=  azim x v u (power_map_points sigma_fan x V E v u j) + azim x v (power_map_points sigma_fan x V E v u j) (power_map_points sigma_fan x V E v u i)`,

REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC"a") THEN USE_THEN "a" MP_TAC 
  THEN REWRITE_TAC[FAN;fan6] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "b") 
  THEN REPEAT STRIP_TAC
THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` (u:real^3)`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
MP_TAC(ISPECL[`(i:num)`; `(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`] image_power_map_points) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
MP_TAC(ISPECL[`(j:num)`; `(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`] image_power_map_points) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
 MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) ((j:num))`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC

  THEN SUBGOAL_THEN `{(u:real^3),power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (j:num),power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) ((i:num))} SUBSET set_of_edge v V E` ASSUME_TAC
THENL[SET_TAC[];

MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (u:real^3)`;` (v:real^3)`]properties_of_graph) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
MP_TAC(ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`]CYCLIC_SET_EDGE_FAN)
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ISPECL[`(x:real^3)`;` (v:real^3)`;`{(u:real^3),power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (j:num),power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) ((i:num))}`;`set_of_edge(v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)` ]subset_cyclic_set_fan)
		THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
MP_TAC(ISPECL[`(i:num)`;` (x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`;` (j:num)`]
AZIM_LE_POWER_SIGMA_FAN)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN

MP_TAC(REAL_ARITH`(azim x v u (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) ((j:num))) < azim x v u (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) ((i:num))))==>(azim x v u (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) ((j:num))) <= azim x v u (power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) ((i:num))))`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN MP_TAC(ISPECL[`x:real^3`;`v:real^3`;`u:real^3`;`power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (j:num)`;`power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) ((i:num))`]sum2_azim_fan) THEN ASM_REWRITE_TAC[]]);;






let SUM1_IFAZIMS_FAN=prove(`!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) (j:num).
FAN(x,V,E) /\ ({v,u} IN E)
/\ ~(set_of_edge v V E ={u})
/\ (j<i)
/\   (i< CARD(set_of_edge v V E)) 
==>
 if_azims_fan x V E v u i= if_azims_fan x V E v u j + azim x v ((power_map_points sigma_fan x V E v u j)) (power_map_points sigma_fan x V E v u i)`,

REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC(ARITH_RULE`(i:num) < CARD(set_of_edge(v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))==> ~(i=CARD(set_of_edge (v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)))`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN MP_TAC(ARITH_RULE`(j:num) < i /\(i:num) < CARD(set_of_edge(v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool))==> ~(j=CARD(set_of_edge(v:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)))`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN 
ASM_REWRITE_TAC[if_azims_fan]
THEN
ASM_MESON_TAC[SUM_AZIM_POWER_SIGMA_FAN]);;





let ULEKUUB=prove(`(!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) (j:num).
FAN(x,V,E) /\ ({v,u} IN E)
/\ ~(set_of_edge v V E ={u})
/\ (j<i)
/\   (i< CARD(set_of_edge v V E)) 
==>
 if_azims_fan x V E v u i= if_azims_fan x V E v u j + azim x v ((power_map_points sigma_fan x V E v u j)) (power_map_points sigma_fan x V E v u i))
/\

(!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3).
FAN(x,V,E) /\ ({v,u} IN E)
/\ ~(set_of_edge v V E ={u})
/\ (1<CARD(set_of_edge v V E ))
==> 
sum (0..(CARD(set_of_edge v V E )-1)) (azim_i_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3))
= &2 *pi)
`,
MESON_TAC[SUM1_IFAZIMS_FAN; SUM_AZIMS_EQ_2PI_FAN]);;






let lemma_disjiont_exists_fan1=prove(` 
!x:real^3 v:real^3 u:real^3 y:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) n:num. 
(y IN complement_set {x,v})/\(if_azim_fan x V E v u 0 <= azim_fan x v u y)/\
(if_azim_fan x V E v u 0 = azim_fan x v u y)/\
(if_azim_fan x V E v u (n) > azim_fan x v u y)/\(CARD E=n)
/\(!i:num. (i IN (0..(n-1)))/\(if_azim_fan x V E v u (i)<if_azim_fan x V E v u (i+1)))
==>(?i. (i IN (0..(n-1)))/\
((if_azim_fan x V E v u (i) = azim_fan x v u y)
\/
((if_azim_fan x V E v u (i) < azim_fan x v u y)
/\(azim_fan x v u y < if_azim_fan x V E v u(i+1)))))`, MESON_TAC[]);;





let lemma_disjiont_exists_fan2=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 n:num. 
 ~(v=x) /\ ~(u=x) /\ (~(collinear {x, v, u})) /\ {v,u} IN E /\ (v IN V) /\ (u IN V) /\ fan (x,V,E)
 ==> if_azims_fan x V E v u (0) = &0`,
REPEAT GEN_TAC THEN REWRITE_TAC[fan;fan1] THEN STRIP_TAC 
  THEN MP_TAC(ISPECL [`v:real^3`; `(V:real^3->bool)`; `(E:(real^3->bool)->bool)`]remark_finite_fan1)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN SUBGOAL_THEN `(u:real^3) IN set_of_edge (v:real^3) (V:real^3->bool)(E:(real^3->bool)->bool)` ASSUME_TAC
  THENL[
    REWRITE_TAC[set_of_edge; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN ` ~( 0 = CARD (set_of_edge (v:real^3) (V:real^3->bool)(E:((real^3)->bool)->bool))) ` ASSUME_TAC
      THENL[
	STRIP_TAC 
	  THEN MP_TAC(ISPEC `set_of_edge (v:real^3) (V:real^3->bool) (E:((real^3)->bool)->bool)`CARD_EQ_0)
	  THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; 
	SUBGOAL_THEN `azim (x:real^3) (v:real^3) (u:real^3) (u:real^3)= &0` ASSUME_TAC
	THENL[ 
	  ASM_MESON_TAC[ azim_is_zero_fan];
	  REWRITE_TAC[if_azims_fan; power_map_points;azim_fan;] THEN ASM_REWRITE_TAC[]]]]);; 






let lemma_disjiont_exists_fan3=prove(
`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 n:num. 
 ~(v=x) /\ ~(u=x) /\ (~(collinear {x, v, u})) /\ {v,u} IN E /\ (v IN V) /\ (u IN V) /\ fan (x,V,E)
 ==> (if_azims_fan x V E v u 0 <= azim_fan x v u y)`,
REPEAT GEN_TAC THEN STRIP_TAC 
  THEN MP_TAC(ISPECL[`x:real^3`; `v:real^3`; `u:real^3`; `y:real^3`] azim) 
  THEN STRIP_TAC 
  THEN MP_TAC(ISPECL[`x:real^3` ; `(V:real^3->bool)`; `(E:(real^3->bool)->bool)` ;`v:real^3` ;`u:real^3`; `n:num`]lemma_disjiont_exists_fan2)
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[azim_fan]);;

let wedge2_fan=new_definition`wedge2_fan (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) =
{y:real^3 | ( if_azims_fan x V E v u i = azim x v u y)/\ ( y IN complement_set {x, v})}`;;

(*wedge2_fan=aff_gt*)


let affine_hull_2_fan= prove(`(!x:real^3 v:real^3. aff {x , v} = {y:real^3| ?t1:real t2:real. (t1 + t2 = &1 )/\ (y = t1 % x + t2 % v )})`,
REWRITE_TAC[aff;AFFINE_HULL_2] THEN SET_TAC[]);;

let AFF_GT_1_1 = prove
 (`!x v.                                                                     
        DISJOINT {x} {v}                                            
        ==> aff_gt {x} {v} =                                       
             {y | ?t1 t2.                                                     
                     &0 < t2 /\
                     t1 + t2 = &1 /\                      
                     y = t1 % x + t2 % v}`, 
  AFF_TAC);;                                                         

let th = prove
 (`!x:real^3 v:real^3 u:real^3 w:real^3.
        ~collinear {x,v,u} /\ ~collinear{x,v,w}
        ==> {y:real^3 | ~collinear {x,v,y} /\ azim x v u w = azim x v u y} = 
            aff_gt {x , v} {w}`,
  GEOM_ORIGIN_TAC `x:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `v:real^3` THEN                         
  X_GEN_TAC `v:real` THEN ASM_CASES_TAC `v = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_LE_LT] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `w:real^3`] THEN
  ASM_CASES_TAC `w:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_CASES_TAC `w:real^3 = v % basis 3` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; COLLINEAR_SPECIAL_SCALE] THEN
  ASM_CASES_TAC `w:real^3 = basis 3` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_GT_SPECIAL_SCALE; IN_SING; FINITE_INSERT; FINITE_EMPTY] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[COLLINEAR_BASIS_3; AZIM_ARG] THEN
  DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN 
  EXISTS_TAC `{y:real^3 | (dropout 3 y:real^2) IN 
                          aff_gt {vec 0} {dropout 3 (w:real^3)}}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    POP_ASSUM MP_TAC THEN
    MAP_EVERY SPEC_TAC
     [`(dropout 3:real^3->real^2) u`,`u:real^2`;
      `(dropout 3:real^3->real^2) v`,`v:real^2`;
      `(dropout 3:real^3->real^2) w`,`w:real^2`;
      `(dropout 3:real^3->real^2) y`,`y:real^2`] THEN
    SIMP_TAC[AFF_GT_1_1; SET_RULE `DISJOINT {x} {y} <=> ~(x = y)`] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN 
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> a /\ c /\ b`] THEN
    REWRITE_TAC[REAL_ARITH `t1 + t2 = &1 <=> t1 = &1 - t2`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN
    ASM_CASES_TAC `y:real^2 = vec 0` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COMPLEX_VEC_0]) THEN
    GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[ARG_EQ; COMPLEX_CMUL; COMPLEX_FIELD 
     `~(w = Cx(&0)) /\ ~(z = Cx(&0)) ==> ~(w / z = Cx(&0))`] THEN
    ASM_SIMP_TAC[COMPLEX_FIELD
     `~(u = Cx(&0)) ==> (w / u = x * y / u <=> w = x * y)`];
    SUBGOAL_THEN `~(w:real^3 = vec 0) /\ ~(w = basis 3)` ASSUME_TAC THENL
     [ASM_MESON_TAC[DROPOUT_BASIS_3; DROPOUT_0]; ALL_TAC] THEN
    ASM_SIMP_TAC[AFF_GT_1_1; AFF_GT_2_1; DISJOINT_INSERT; IN_INSERT;
                 DISJOINT_EMPTY; NOT_IN_EMPTY] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> a /\ c /\ b`] THEN
    REWRITE_TAC[REAL_ARITH `t1 + t2 = &1 <=> t1 = &1 - t2`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL] THEN      
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH; DIMINDEX_2;
             DROPOUT_BASIS_3; FORALL_2; dropout; LAMBDA_BETA] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC[REAL_ARITH `y = t * &1 + s <=> t = y - s`; EXISTS_REFL]]);;



let th1=prove(`(!x:real^3 v:real^3 u:real^3 w:real^3 t1:real t2:real t3:real. (t3 > &0) /\ (t1 + t2 + t3 = &1)
/\ DISJOINT {x,v} {w} /\ ~collinear {x,v,u}/\ ~collinear {x,v,w}
 ==> azim x v u w =
 azim x v u (t1 % x + t2 % v + t3 % w))`,
REPEAT GEN_TAC THEN STRIP_TAC THEN ASSUME_TAC(AFF_GT_2_1) 
THEN POP_ASSUM(MP_TAC o ISPECL [`x:real^3`;`v:real^3`;`w:real^3`]) 
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC 
THEN ABBREV_TAC `(y:real^3)= (t1:real)  % (x:real^3) + (t2:real) % (v:real^3) + (t3:real) % (w:real^3)`
      THEN SUBGOAL_THEN `(y:real^3) IN aff_gt {(x:real^3),(v:real^3)} {w:real^3}` ASSUME_TAC
THENL[
ASM_REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `t1:real` 
THEN EXISTS_TAC `t2:real` THEN EXISTS_TAC `t3:real`
THEN EXPAND_TAC "y" THEN ASM_MESON_TAC[REAL_ARITH`(a:real)> &0 <=> &0 < a ` ];
						
 POP_ASSUM MP_TAC THEN
ASSUME_TAC(th) THEN POP_ASSUM(MP_TAC o ISPECL [`x:real^3`;`v:real^3`;`u:real^3`;`w:real^3`]) 
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN POP_ASSUM (fun th-> REWRITE_TAC[SYM(th)]) 
THEN REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[]]);;

  let th2= prove(`!x:real^3 v:real^3 w:real^3. ~(x=v)==>  (w IN complement_set {x,v}==> ~ collinear {x,v,w})`,   
REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[CONTRAPOS_THM; COLLINEAR_3;COLLINEAR_LEMMA; complement_set; IN_ELIM_THM;affine_hull_2_fan] THEN STRIP_TAC
THENL[
ASM_MESON_TAC[VECTOR_ARITH`(x-v= vec 0)<=> (x=v)`];
 EXISTS_TAC `&0` THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_ARITH`&0+ &1 = &1`; VECTOR_ARITH`&0 % x= vec 0`; VECTOR_ARITH`w=vec 0 + &1 % v <=> w - v = vec 0`] THEN SET_TAC[];
EXISTS_TAC `c:real` THEN EXISTS_TAC `&1 - (c:real)` THEN REWRITE_TAC[REAL_ARITH`c+ &1 - c = &1`; VECTOR_ARITH`w=c % x  + (&1 - c) % v <=> w - v = c % (x-v)`] THEN SET_TAC[]]);;





let COMPLEMENT_SET_FAN=prove(`!x:real^3 v:real^3 u:real^3 y:real^3 w:real^3 t1:real t2:real t3:real. 
~( w IN aff {x, v}) /\ ~(t3 = &0) /\ (t1 + t2 + t3 = &1)
==> t1 % x + t2 % v + t3 % w IN
 complement_set {x, v}`,
 REPEAT GEN_TAC THEN ASSUME_TAC(affine_hull_2_fan) THEN STRIP_TAC THEN 
REWRITE_TAC[complement_set; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN 
REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
  THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN  ` (t3:real) % w =((t1':real)- (t1:real)) % (x:real^3) + ((t2':real)- (t2:real)) % (v:real^3) ` ASSUME_TAC
 THENL
  [POP_ASSUM MP_TAC THEN VECTOR_ARITH_TAC;
   REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN(LABEL_TAC "b") THEN DISCH_THEN(LABEL_TAC "c") THEN DISCH_THEN(LABEL_TAC "d")
     THEN REPEAT STRIP_TAC THEN USE_THEN "c" MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN
     EXISTS_TAC `((t1':real) - (t1:real))/(t3:real)` THEN EXISTS_TAC `((t2':real) - (t2:real))/(t3:real)`
     THEN SUBGOAL_THEN  `((t1':real) - (t1:real))/(t3:real)+ ((t2':real) - (t2:real))/(t3:real) = &1` ASSUME_TAC  THENL
        [REWRITE_TAC[real_div] THEN REWRITE_TAC[REAL_ARITH `a*b+c*b=(a+c)*b`] THEN
        SUBGOAL_THEN `(t1':real) - (t1:real) + (t2':real) - (t2:real) - (t3:real) = &0` ASSUME_TAC THENL
           [REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
            SUBGOAL_THEN `(t1':real) - (t1:real) + (t2':real) - (t2:real) = (t3:real)` ASSUME_TAC THENL
              [POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
               ASM_MESON_TAC[REAL_MUL_RINV]]]; 
       ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN
       REWRITE_TAC[VECTOR_ARITH ` (((t1':real) - (t1:real)) * inv (t3:real)) % (x:real^3) + (((t2':real) - (t2:real)) * inv t3) % (v:real^3) = inv t3 % ((t1' - t1) % x + (t2' - t2) % v)`] THEN 
       SUBGOAL_THEN `(t3:real) % (w:real^3) = t3 %( inv t3 % (((t1':real) - (t1:real)) % (x:real^3) + ((t2':real) - (t2:real)) % (v:real^3)))` ASSUME_TAC  THENL
                  [REWRITE_TAC[VECTOR_ARITH ` (t3:real) % (inv t3 % (((t1':real) - (t1:real)) % (x:real^3) + ((t2':real) - (t2:real)) % (v:real^3)))= (t3 * inv t3) % ((t1' - t1) % x + (t2' - t2)  % v) `] THEN
                   SUBGOAL_THEN `((t3:real) * inv (t3:real) = &1) ` ASSUME_TAC THENL
                                  [ASM_MESON_TAC[REAL_MUL_RINV]; 
                                    ASM_REWRITE_TAC[]  THEN VECTOR_ARITH_TAC];
                 ASM_MESON_TAC[VECTOR_MUL_LCANCEL_IMP]]]]);;


let aff_gt_subset_wedge_fan2=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num.  
 ~(i= CARD (set_of_edge v V E))
/\  ~collinear {x,v,u} /\ ~collinear {x,v, power_map_points sigma_fan x V E v u i}
==> 
 aff_gt {x , v} {power_map_points sigma_fan x V E v u i}  SUBSET wedge2_fan x V E v u i `,

REWRITE_TAC[SUBSET] THEN REPEAT GEN_TAC THEN 
ASSUME_TAC(affine_hull_2_fan)
THEN STRIP_TAC THEN ASSUME_TAC(th3) 
THEN  POP_ASSUM (MP_TAC o ISPECL [`x:real^3`;`v:real^3`;`(power_map_points sigma_fan (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num))`]) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THEN ASSUME_TAC(AFF_GT_2_1) 
  THEN  POP_ASSUM (MP_TAC o ISPECL [`x:real^3`;`v:real^3`;`(power_map_points sigma_fan (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num))`]) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] 
THEN GEN_TAC THEN REWRITE_TAC[wedge2_fan; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN 
REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `~((t3:real) = &0)` ASSUME_TAC
THENL
   [REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
ASSUME_TAC(th1) 
THEN POP_ASSUM( MP_TAC o ISPECL[`x:real^3`;` v:real^3`;` u:real^3`;` power_map_points sigma_fan x V E v u i` ;`t1:real` ;`t2:real` ;`t3:real`])
  THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
SUBGOAL_THEN `t1 % x + t2 % v + t3 % power_map_points sigma_fan x V E v u i IN
 complement_set {x, v}` ASSUME_TAC
THENL
      [ASM_MESON_TAC[COMPLEMENT_SET_FAN];
ASM_REWRITE_TAC[] THEN REWRITE_TAC[if_azims_fan;]
THEN ASM_MESON_TAC[REAL_ARITH`((t3:real)> &0) <=> (&0 < t3)`]]]);;



let wedge_fan2_subset_aff_gt=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num. 
 ~collinear {x,v,u} /\ ~collinear {x, v, power_map_points sigma_fan x V E v u i}
/\  ~(i= CARD (set_of_edge v V E)) 
==>
wedge2_fan x V E v u i SUBSET aff_gt {x , v} {power_map_points sigma_fan x V E v u i}`,
REPEAT GEN_TAC THEN 
ASSUME_TAC(affine_hull_2_fan) THEN
STRIP_TAC THEN ASSUME_TAC(th3) 
THEN  POP_ASSUM (MP_TAC o ISPECL [`x:real^3`;`v:real^3`;`(power_map_points sigma_fan (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num))`]) 
THEN ASM_REWRITE_TAC[] THEN STRIP_TAC
THEN ASSUME_TAC(AFF_GT_2_1) 
  THEN  POP_ASSUM (MP_TAC o ISPECL [`x:real^3`;`v:real^3`;`(power_map_points sigma_fan (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num))`])
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]
 THEN REWRITE_TAC[SUBSET] THEN GEN_TAC 
  THEN REWRITE_TAC[wedge2_fan;IN_ELIM_THM] THEN REWRITE_TAC[if_azims_fan; azim] THEN ASM_REWRITE_TAC[]
THEN STRIP_TAC
  THEN ASSUME_TAC(th2) THEN POP_ASSUM(MP_TAC o ISPECL[`x:real^3`; `v:real^3`;`x':real^3`]) 
THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
  THEN ASSUME_TAC(th)
THEN POP_ASSUM (MP_TAC o SPECL [`x:real^3`;`v:real^3`;`u:real^3`;`(power_map_points sigma_fan x  (V:real^3->bool) (E:(real^3->bool)->bool) v u (i:num)):real^3`;]) THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION] THEN DISCH_TAC 
  THEN POP_ASSUM (MP_TAC o ISPEC `x':real^3`)THEN  
 REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]);;



let wedge_fan2_equal_aff_gt=prove(
` !x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num.
 ~collinear {x,v,u} /\ ~collinear {x, v, power_map_points sigma_fan x V E v u i}
/\  ~(i= CARD (set_of_edge v V E)) 
==>
 wedge2_fan x V E v u i = aff_gt {x , v} {power_map_points sigma_fan x V E v u i}    `,
REPEAT GEN_TAC THEN STRIP_TAC THEN
SUBGOAL_THEN `wedge2_fan x V E v u i SUBSET aff_gt {x , v} {power_map_points sigma_fan x V E v u i}` ASSUME_TAC
THENL
  [ ASM_MESON_TAC[ wedge_fan2_subset_aff_gt;aff_gt_subset_wedge_fan2];
   SUBGOAL_THEN `
      aff_gt {(x:real^3), (v:real^3)} {power_map_points sigma_fan (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)}  SUBSET wedge2_fan (x:real^3) V E (v:real^3) (u:real^3) (i:num)` ASSUME_TAC
THENL[ASM_MESON_TAC[aff_gt_subset_wedge_fan2];
      SET_TAC[]]]);;


let wedge_fan2_equal_aff_gt_fan=prove(` !x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num.
FAN(x,V,E)/\ ({v,u} IN E)
/\  ~(i= CARD (set_of_edge v V E)) 
==>
 wedge2_fan x V E v u i = aff_gt {x , v} {power_map_points sigma_fan x V E v u i}    `,

 REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN DISCH_THEN (LABEL_TAC"a") THEN USE_THEN "a" MP_TAC 
  THEN REWRITE_TAC[FAN;fan6] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "b") 
  THEN REPEAT STRIP_TAC
THEN MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` (u:real^3)`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
MP_TAC(ISPECL[`(i:num)`; `(x:real^3)`;` (V:real^3->bool)`;
` (E:(real^3->bool)->bool)`;` (v:real^3)`;` (u:real^3)`] image_power_map_points) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN
 MP_TAC (ISPECL[`(x:real^3)`;` (V:real^3->bool)`;` (E:(real^3->bool)->bool)`;`(v:real^3)`;` power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num)`]properties_of_set_of_edge_fan)
THEN  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN USE_THEN "b" (fun th-> MP_TAC(ISPEC`{(v:real^3),(u:real^3)}`th))  THEN REMOVE_THEN "b" (fun th-> MP_TAC(ISPEC`{(v:real^3),(power_map_points sigma_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num))}`th)) THEN ASM_REWRITE_TAC[SET_RULE`{a} UNION {b,c}={a,b,c}`] THEN DISCH_TAC THEN DISCH_TAC THEN ASM_MESON_TAC[wedge_fan2_equal_aff_gt]);;






(************)

(*let wedge3_fan=new_definition`wedge3_fan (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) =
{y:real^3 | ( if_azims_fan x V E v u (i) < azim x v u y)/\
(azim x v u y < if_azims_fan x V E v u (SUC i)) /\( y IN complement_set {x, v})}`;;




let wedge4_fan=new_definition`wedge4_fan (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) ={y:real^3 | (( if_azims_fan x V E v u (i) = azim_fan x v u y)\/(( if_azims_fan x V E v u (i) < azim_fan x v u y)/\(azim_fan x v u y < if_azims_fan x V E v u (i+1))))/\( y IN complement_set {x, v})}`;;


let lemma_disjiont_union=prove(`!(x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num). 
wedge4_fan x V E v u i=wedge2_fan x V E v u i UNION wedge3_fan x V E v u i`, 
REWRITE_TAC[wedge2_fan;wedge3_fan;wedge4_fan;FUN_EQ_THM; UNION] THEN GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM]
THEN MESON_TAC[]);;



let wedges_fan= new_recursive_definition num_RECURSION `
(wedges_fan (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)  0 = wedge4_fan x V E v u (0))/\(wedges_fan x V E v u (SUC n)=(wedges_fan x V E v u n) UNION wedge4_fan x V E v u (SUC n))`;;


let complement_setser=new_definition`complement_setser (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)  (n:num)=
{ y|(y IN complement_set {x,v})/\
(if_azims_fan x V E v u (0) < azim_fan x v u y)/\
(if_azims_fan x V E v u (0) = azim_fan x v u y)/\
(&2 * pi > azim_fan x v u y)/\
(!i. (i IN (0..(n-1)))/\(if_azims_fan x V E v u (i) < if_azims_fan x V E v u (i+1))) } `;;



let lemma_disjiont_union1=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3  n:num. 
(y IN complement_setser x V E v u n) ==>(?i. (i IN (0..(n-1)))/\( y IN (wedge4_fan x V E v u i)))`,
REPEAT GEN_TAC THEN
REWRITE_TAC[complement_setser; wedge4_fan] THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;


let lemma_disjiont_union2=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 n. 
(?i. (i IN (0..(n-1)))/\ (y IN (wedge4_fan x V E v u i))) ==> (y IN complement_set {x,v}) `, REPEAT GEN_TAC THEN REWRITE_TAC[complement_set; wedge4_fan] THEN
REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;






let lemma_disjiont_unions=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 n:num.(y IN UNIONS {wedge4_fan x V E v u i| i IN (0..(n-1))}) <=> 
(?i. (i IN (0..(n-1)))/\ (y IN (wedge4_fan x V E v u i)))  `,
REWRITE_TAC[UNIONS] THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;



let lemma_disjiont_unions2=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 n:num. 
(y IN UNIONS {wedge4_fan x V E v u i | i IN (0..(n-1))}) ==>(y IN complement_set {x,v}) `,
REPEAT GEN_TAC THEN STRIP_TAC THEN 
SUBGOAL_THEN `(?i. (i IN (0..(n-1)))/\ (y IN (wedge4_fan x V E v u i)))` ASSUME_TAC 
THENL
  [POP_ASSUM MP_TAC THEN MESON_TAC[lemma_disjiont_unions];
   POP_ASSUM MP_TAC THEN MESON_TAC[lemma_disjiont_union2]]);;






let lemma_disjiont_unions1= prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 n:num.
(y IN complement_setser x V E v u n) ==> (y IN UNIONS {wedge4_fan x V E v u i | i IN (0..(n-1))})`,
REPEAT GEN_TAC THEN STRIP_TAC THEN 
SUBGOAL_THEN `(?i. (i IN (0..(n-1))) /\ (y IN (wedge4_fan x V E v u i)))` ASSUME_TAC
THENL 
   [POP_ASSUM MP_TAC THEN MESON_TAC[lemma_disjiont_union1];
     POP_ASSUM MP_TAC THEN MESON_TAC[lemma_disjiont_unions]]);;








let disjiont_union1=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3  n:num.
complement_setser x V E v u n = complement_set {x,v}==>
(!y. ((y IN UNIONS {wedge4_fan x V E v u i | i IN (0..(n-1))})<=>(y IN complement_set {x,v})))`,
REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN EQ_TAC 
THENL 
  [MESON_TAC[lemma_disjiont_unions2];
   SUBGOAL_THEN `(y IN complement_setser x V E v u n) ==> (y IN UNIONS {wedge4_fan x V E v u i | i IN (0..(n-1))})` ASSUME_TAC
      THENL 
        [MESON_TAC[lemma_disjiont_unions1]; 
         REPEAT (POP_ASSUM MP_TAC) THEN MESON_TAC[]]]);;


let disjiont_union2=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 n:num.
complement_setser x V E v u n = complement_set {x,v}==>
(UNIONS {wedge4_fan x V E v u i | i IN (0..(n-1))}= complement_set {x,v})`, 
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
SUBGOAL_THEN `(!y. ((y IN UNIONS {wedge4_fan x V E v u i | i IN (0..(n-1))})<=>(y IN complement_set {x,v})))` ASSUME_TAC
THENL 
  [POP_ASSUM MP_TAC THEN MESON_TAC[disjiont_union1]; 
   POP_ASSUM MP_TAC THEN REWRITE_TAC[IN]]);;



let lemma_disjiont1=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 n:num.
(complement_setser x V E v u n = complement_set {x,v})==>
((UNIV:real^3->bool) = aff {x,v} UNION (UNIONS {wedge4_fan x V E v u i | i IN (0..(n-1))}))`, 
REPEAT GEN_TAC THEN STRIP_TAC THEN
SUBGOAL_THEN `(UNIONS {wedge4_fan x V E v u i | i IN (0..(n-1))} = complement_set {x,v})` ASSUME_TAC 
THENL 
 [POP_ASSUM MP_TAC THEN MESON_TAC[disjiont_union2];
 SUBGOAL_THEN `(UNIV:real^3->bool) = aff{x, v} UNION  complement_set {x, v}` ASSUME_TAC
     THENL
       [MESON_TAC[union_aff];
        REPEAT (POP_ASSUM MP_TAC) THEN MESON_TAC[]]]);;



let lemma_disjiont1a=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 n:num.
(complement_setser x V E v u n = complement_set {x,v})==>
((UNIV:real^3->bool) = aff {x,v} UNION (UNIONS {wedge2_fan x V E v u i UNION wedge3_fan x V E v u i | i IN (0..(n-1))}))`,
SUBGOAL_THEN `!x V E v u i. wedge4_fan x V E v u i =wedge2_fan x V E v u i UNION wedge3_fan x V E v u i` ASSUME_TAC THENL
 [MESON_TAC[ lemma_disjiont_union];
  REPEAT GEN_TAC  THEN DISCH_TAC THEN 
  SUBGOAL_THEN `((UNIV:real^3->bool) = aff {x,v} UNION (UNIONS {wedge4_fan x V E v u i | i IN (0..(n-1))}))` ASSUME_TAC
     THENL [ASM_MESON_TAC[ lemma_disjiont1];
            POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[]]]);;





let disjiont_cor6dot1=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num. 
wedge2_fan x V E v u i INTER wedge3_fan x V E v u i={}`,
REPEAT GEN_TAC THEN REWRITE_TAC[wedge2_fan;wedge3_fan;FUN_EQ_THM] THEN GEN_TAC THEN 
REWRITE_TAC[INTER; EMPTY; IN_ELIM_THM] THEN
STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN(LABEL_TAC "a") THEN 
DISCH_THEN(LABEL_TAC "b") THEN
DISCH_THEN(LABEL_TAC "c") THEN
DISCH_THEN(LABEL_TAC "d") THEN
USE_THEN "a" MP_TAC THEN
USE_THEN "c" MP_TAC THEN
REAL_ARITH_TAC);;




let disjiont_cor6dot1a=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool)v:real^3 u:real^3 i:num j:num. 
(if_azims_fan x V E v u i <= if_azims_fan x V E v u j) ==> 
(wedge2_fan x V E v u i INTER wedge3_fan x V E v u j={})`,
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wedge2_fan;wedge3_fan;FUN_EQ_THM] THEN GEN_TAC THEN 
REWRITE_TAC[INTER; EMPTY; IN_ELIM_THM] THEN
STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN(LABEL_TAC "a") THEN 
DISCH_THEN(LABEL_TAC "b") THEN
DISCH_THEN(LABEL_TAC "c") THEN
DISCH_THEN(LABEL_TAC "d") 
THEN DISCH_THEN(LABEL_TAC "f") THEN
SUBGOAL_THEN `(if_azims_fan x V E v u j < if_azims_fan x V E v u i)` ASSUME_TAC
THENL
  [ASM_REWRITE_TAC[];
    POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC "g") THEN USE_THEN "a" MP_TAC THEN
USE_THEN "g" MP_TAC THEN REAL_ARITH_TAC]);;




let disjiont_cor6dot1b=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num j:num. 
(if_azims_fan x V E v u (j+1) <= if_azims_fan x V E v u i) ==> 
(wedge2_fan x V E v u i INTER wedge3_fan x V E v u j={})`,
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wedge2_fan;wedge3_fan;FUN_EQ_THM] THEN GEN_TAC THEN 
REWRITE_TAC[INTER; EMPTY; IN_ELIM_THM] THEN
STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN(LABEL_TAC "a") THEN 
DISCH_THEN(LABEL_TAC "b") THEN
DISCH_THEN(LABEL_TAC "c") THEN
DISCH_THEN(LABEL_TAC "d") 
THEN DISCH_THEN(LABEL_TAC "f") THEN
SUBGOAL_THEN `(if_azims_fan x V E v u i < if_azims_fan x V E v u (j+1))` ASSUME_TAC
THENL
  [ASM_REWRITE_TAC[];
    POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC "g")
      THEN USE_THEN "a" MP_TAC THEN
      USE_THEN "g" MP_TAC THEN REAL_ARITH_TAC]);;



let disjiont_cor6dot1c= prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num j:num.
(if_azims_fan x V E v u (j+1) <= if_azims_fan x V E v u i)\/(if_azims_fan x V E v u i <= if_azims_fan x V E v u j) ==> 
(wedge2_fan x V E v u i INTER wedge3_fan x V E v u j={})`,
REPEAT GEN_TAC THEN STRIP_TAC 
THENL 
     [POP_ASSUM MP_TAC THEN MESON_TAC[disjiont_cor6dot1b];
      POP_ASSUM MP_TAC THEN MESON_TAC[disjiont_cor6dot1a]]);;





let disjiont1_cor6dot1 = prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num. 
wedge3_fan x V E v u i INTER aff {x,v}={}`,
REPEAT GEN_TAC THEN REWRITE_TAC[wedge3_fan; INTER] THEN REWRITE_TAC[complement_set; FUN_EQ_THM; EMPTY] THEN
GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC
  THEN MESON_TAC[]);;


let disjiont2_cor6dot1=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num. 
wedge3_fan x V E v u i INTER (aff {x,v} UNION wedge2_fan x V E v u i)={}`,
REPEAT GEN_TAC THEN REWRITE_TAC[UNION_OVER_INTER] THEN SUBGOAL_THEN `wedge3_fan x V E v u i INTER aff {x,v}={}` ASSUME_TAC
    THENL [MESON_TAC[disjiont1_cor6dot1];
          SUBGOAL_THEN `wedge2_fan x V E v u i INTER wedge3_fan x V E v u i={}` ASSUME_TAC
          THENL
              [MESON_TAC[disjiont_cor6dot1];
               SET_TAC[]]]);;


let disjiont2_cor6dot1a=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num. 
((if_azims_fan x V E v u (j+1) <= if_azims_fan x V E v u i)\/(if_azims_fan x V E v u i <= if_azims_fan x V E v u j))==>
(wedge3_fan x V E v u j INTER (aff {x,v} UNION wedge2_fan x V E v u i)={})`,
REPEAT GEN_TAC THEN REWRITE_TAC[UNION_OVER_INTER] THEN DISCH_TAC THEN 
SUBGOAL_THEN `wedge3_fan x V E v u j INTER aff {x,v}={}` ASSUME_TAC
    THENL 
       [MESON_TAC[disjiont1_cor6dot1];
        SUBGOAL_THEN `wedge2_fan x V E v u i INTER wedge3_fan x V E v u j={}` ASSUME_TAC
       THENL
          [ REPEAT(POP_ASSUM MP_TAC) THEN 
            DISCH_THEN (LABEL_TAC "a") THEN 
            DISCH_THEN(LABEL_TAC "b")  THEN
            USE_THEN "a" MP_TAC THEN MESON_TAC[disjiont_cor6dot1c];
                SET_TAC[]]]);;


(*******************[cor:W]*************************)






let aff_ge_subset_aff_gt_union_aff=prove(`!x:real^3 v:real^3 w:real^3. 
(!x:real^3 v:real^3. aff {x , v} = {y:real^3| ?t1:real t2:real. (t1 + t2 = &1 )/\ (y = t1 % x + t2 % v )})
/\ (!x:real^3 v:real^3 w:real^3. aff_gt {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 > &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
/\ (!x:real^3 v:real^3 w:real^3. aff_ge {x} {v, w}={y:real^3 |  ?t1:real t2:real t3:real. (t2 >= &0)/\ (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
==> 
 aff_ge {x} {v , w} SUBSET  (aff_gt {x , v} {w}) UNION (aff {x, v})   `,
REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; UNION; IN_ELIM_THM] THEN GEN_TAC THEN
REWRITE_TAC[REAL_ARITH `((t3:real) >= &0) <=> (t3 > &0) \/ ( t3 = &0)`; TAUT `(a \/ b) /\ (c \/ d) /\ e /\ f <=> ((a \/ b)/\ c /\ e /\ f) \/ ((a \/ b) /\ d /\ e /\ f)`; EXISTS_OR_THM] THEN MATCH_MP_TAC MONO_OR THEN
SUBGOAL_THEN `((?t1:real t2:real t3:real.
       (t2 > &0 \/ t2 = &0) /\
       t3 > &0 /\
       t1 + t2 + t3 = &1 /\
       (x':real^3) = t1 % x + t2 % v + t3 % w)
  ==> (?t1 t2 t3.
           t3 > &0 /\ t1 + t2 + t3 = &1 /\ x' = t1 % x + t2 % v + t3 % w))` ASSUME_TAC THENL
    [MESON_TAC[];
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
     REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN
     REWRITE_TAC[REAL_ARITH `((t2:real) > &0 \/ (t2 = &0)) <=> (t2 >= &0)`] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
     POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
     REWRITE_TAC [REAL_ARITH `(a:real)+ &0 = a`; VECTOR_ARITH  `&0 % (w:real^3) = vec 0`; 
     VECTOR_ARITH `  ((x':real^3) = (t1:real) % (x:real^3) + (t2:real) % (v:real^3) + vec 0)<=> ( x' = t1 % x + t2 % v )` ]
       THEN MESON_TAC[]]);;







let aff_ge_subset_wedge_fan2_union_aff=prove(`
(!x:real^3 v:real^3. aff {x , v} = {y:real^3| ?t1:real t2:real. (t1 + t2 = &1 )/\ (y = t1 % x + t2 % v )}) 
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. aff_gt {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 > &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
/\ (!x:real^3 v:real^3 u:real^3 w:real^3 t1:real t2:real t3:real. ~(t3 = &0) /\ (t1 + t2 + t3 = &1)  ==> azim x v u w =
 azim x v u (t1 % x + t2 % v + t3 % w))
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. {y:real^3 |  azim x v u w =
 azim x v u y}=aff_gt {x , v} {w})
/\ (!x:real^3 v:real^3 w:real^3. aff_ge {x} {v, w}={y:real^3 |  ?t1:real t2:real t3:real. (t2 >= &0)/\ (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
==> 
(!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num.  
~(i= CARD (set_of_edge v V E))
/\ ~( (power_map_points sigma_fan x V E v u i) IN aff {x, v})
==>
 aff_ge {x} {v , (power_map_points sigma_fan x V E v u i)} SUBSET   (wedge2_fan x V E v u i)  UNION (aff {x, v}))   `,
DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
SUBGOAL_THEN ` wedge2_fan x V E v u i = aff_gt {(x:real^3) , (v:real^3)} {power_map_points sigma_fan x V E (v:real^3) (u:real^3) (i:num)}` ASSUME_TAC
THENL 
     [ASSUME_TAC(wedge_fan2_equal_aff_gt) THEN POP_ASSUM MP_TAC 
	THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC 
	THEN POP_ASSUM (MP_TAC o ISPECL [`x:real^3`; `(V:real^3->bool)`; `(E:(real^3->bool)->bool)`; `v:real^3`; `u:real^3`; `i:num`  ]) 
	THEN ASM_REWRITE_TAC[];
      POP_ASSUM (fun th -> REWRITE_TAC[th] THEN (ASSUME_TAC th)) THEN
      ASM_MESON_TAC[ aff_ge_subset_aff_gt_union_aff]]);;
  



let disjiont_aff_ge_wedge_fan3=prove(`
(!x:real^3 v:real^3. aff {x , v} = {y:real^3| ?t1:real t2:real. (t1 + t2 = &1 )/\ (y = t1 % x + t2 % v )}) 

/\ (!x:real^3 v:real^3 u:real^3 w:real^3. aff_gt {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 > &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
/\ (!x:real^3 v:real^3 u:real^3 w:real^3 t1:real t2:real t3:real. ~(t3 = &0) /\ (t1 + t2 + t3 = &1)  ==> azim x v u w =
 azim x v u (t1 % x + t2 % v + t3 % w))
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. {y:real^3 |  azim x v u w =
 azim x v u y}=aff_gt {x , v} {w})
/\ (!x:real^3 v:real^3 w:real^3. aff_ge {x} {v, w}={y:real^3 |  ?t1:real t2:real t3:real. (t2 >= &0)/\ (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
==> 
(!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num. 
~(i= CARD (set_of_edge v V E))
/\
~( (power_map_points sigma_fan x V E v u i) IN aff {x, v})
==>
( aff_ge {x} {v , (power_map_points sigma_fan x V E v u i)})  INTER (wedge3_fan x V E v u i) = {} )`,
 
STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
SUBGOAL_THEN ` aff_ge {(x:real^3)} {(v:real^3) , (power_map_points sigma_fan x V E v (u:real^3) (i:num))} SUBSET   (wedge2_fan x V E v u i)  UNION (aff {x, v})   ` ASSUME_TAC
THENL
  [ASSUME_TAC(aff_ge_subset_wedge_fan2_union_aff) THEN POP_ASSUM MP_TAC 
     THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC 
	THEN POP_ASSUM (MP_TAC o ISPECL [`x:real^3`; `(V:real^3->bool)`; `(E:(real^3->bool)->bool)`; `v:real^3`; `u:real^3`; `i:num`  ]) 
	THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN `wedge3_fan x V E v u i INTER (aff {x,v} UNION wedge2_fan x V E v u i)={}` ASSUME_TAC
    THENL
       [MESON_TAC[disjiont2_cor6dot1];
        SET_TAC[]]]);;



let disjiont_aff_ge_wedge_fan3a=prove(`
(!x:real^3 v:real^3. aff {x , v} = {y:real^3| ?t1:real t2:real. (t1 + t2 = &1 )/\ (y = t1 % x + t2 % v )}) 

/\ (!x:real^3 v:real^3 u:real^3 w:real^3. aff_gt {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 > &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
/\ (!x:real^3 v:real^3 u:real^3 w:real^3 t1:real t2:real t3:real. ~(t3 = &0) /\ (t1 + t2 + t3 = &1)  ==> azim x v u w =
 azim x v u (t1 % x + t2 % v + t3 % w))
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. {y:real^3 |  azim x v u w =
 azim x v u y}=aff_gt {x , v} {w})
/\ (!x:real^3 v:real^3 w:real^3. aff_ge {x} {v, w}={y:real^3 |  ?t1:real t2:real t3:real. (t2 >= &0)/\ (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
/\ (!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num j:num. 
(if_azims_fan x V E v u (j+1) <= if_azims_fan x V E v u i)\/(if_azims_fan x V E v u i <= if_azims_fan x V E v u j))
==>
(!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num j:num. 
~(i= CARD (set_of_edge v V E))
/\ ~( (power_map_points sigma_fan x V E v u i) IN aff {x, v})
==>
(( aff_ge {x} {v , (power_map_points sigma_fan x V E v u i)}) INTER (wedge3_fan x V E v u j) = {})) `,

STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
SUBGOAL_THEN ` aff_ge {(x:real^3)} {(v:real^3) , (power_map_points sigma_fan x (V:real^3->bool) (E:(real^3->bool)->bool) v (u:real^3) (i:num))} SUBSET   (wedge2_fan x V E v u i)  UNION (aff {x, v})   ` ASSUME_TAC 
THENL
  [ASSUME_TAC(aff_ge_subset_wedge_fan2_union_aff) THEN POP_ASSUM MP_TAC 
     THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC 
	THEN POP_ASSUM (MP_TAC o ISPECL [`x:real^3`; `(V:real^3->bool)`; `(E:(real^3->bool)->bool)`; `v:real^3`; `u:real^3`; `i:num` ]) 
	THEN ASM_REWRITE_TAC[];
   SUBGOAL_THEN `wedge3_fan x (V:real^3->bool) (E:(real^3->bool)->bool) v u j INTER (aff {x,v} UNION wedge2_fan x V E v u i)={}` ASSUME_TAC
     THENL
       [ASSUME_TAC(disjiont2_cor6dot1a) THEN POP_ASSUM MP_TAC 
     THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC 
	THEN POP_ASSUM (MP_TAC o ISPECL [`x:real^3`; `(V:real^3->bool)`; `(E:(real^3->bool)->bool)`; `v:real^3`; `u:real^3`; `i:num`]) 
	THEN ASM_REWRITE_TAC[];
        SET_TAC[]]]);;






(*************JGIYDLE*******************)

let rcone_fan = new_definition `rcone_fan  (x:real^3) (v:real^3) (h:real) = {y:real^3 | (y-x) dot (v-x) >(dist(y,x)*dist(v,x)*h)}`;;


let wedge5_fan=new_definition`wedge5_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) (h:real)= wedge3_fan x V E v u i INTER rcone_fan x v h`;;





let lemma_4dot31=prove(`(!x:real^3 v:real^3. aff {x , v} = {y:real^3| ?t1:real t2:real. (t1 + t2 = &1 )/\ (y = t1 % x + t2 % v )}) 
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. aff_gt {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 > &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
/\ (!x:real^3 v:real^3 u:real^3 w:real^3 t1:real t2:real t3:real. ~(t3 = &0) /\ (t1 + t2 + t3 = &1)  ==> azim x v u w =
 azim x v u (t1 % x + t2 % v + t3 % w))
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. {y:real^3 |  azim x v u w =
 azim x v u y}=aff_gt {x , v} {w})
/\ (!x:real^3 v:real^3 w:real^3. aff_ge {x} {v, w}={y:real^3 |  ?t1:real t2:real t3:real. (t2 >= &0)/\ (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
/\ (!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num j:num. 
(if_azims_fan x V E v u (j+1) <= if_azims_fan x V E v u i)\/(if_azims_fan x V E v u i <= if_azims_fan x V E v u j))
==>
(!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3  i:num j:num h:real. 
~(i= CARD (set_of_edge v V E))
/\
~( (power_map_points sigma_fan x V E v u i) IN aff {x, v})
==>
(( aff_ge {x} {v , (power_map_points sigma_fan x V E  v u i)}) INTER (wedge5_fan x V E v u j h) = {})) `,

STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[wedge5_fan] THEN
SUBGOAL_THEN `(( aff_ge {(x:real^3)} {(v:real^3) , (power_map_points sigma_fan x (V:real^3->bool) (E:(real^3->bool)->bool) v (u:real^3) (i:num))}) INTER (wedge3_fan (x:real^3) V E v u (j:num)) = {})` ASSUME_TAC  
THENL
  [ASSUME_TAC(disjiont_aff_ge_wedge_fan3a) THEN POP_ASSUM MP_TAC 
     THEN POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC 
	THEN POP_ASSUM (MP_TAC o ISPECL [`x:real^3`; `(V:real^3->bool)`; `(E:(real^3->bool)->bool)`; `v:real^3`; `u:real^3`; `i:num`; `j:num` ]) 
	THEN ASM_REWRITE_TAC[];
   SET_TAC[]]);;




(*---------------------------------------------------------------------------------*)
(*     aff_ge {x} {v , w}) = (aff_ge {x , v} {w}) INTER (aff_ge {x , w} {v})       *)
(*---------------------------------------------------------------------------------*)

let aff_ge_inter_aff_ge=prove(`
(!x:real^3 v:real^3 w:real^3. aff_ge {x} {v , w}={y:real^3 |  ?t1:real t2:real t3:real. (t2 >= &0)/\ (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)}) 
/\ 
(!x:real^3 v:real^3 w:real^3. aff_ge {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
==> 
(!x:real^3 v:real^3 w:real^3. 
(!a:real b:real c:real. a % x + b % v + c % w = vec 0 ==> a = &0 /\ b = &0 /\ c = &0  )
==>
(aff_ge {x} {v , w}) = (aff_ge {x , v} {w}) INTER (aff_ge {x , w} {v}))`,
STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[INTER; IN_ELIM_THM; FUN_EQ_THM; IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC 

THENL
   [STRIP_TAC THEN SUBGOAL_THEN `?t1:real t2:real t3:real. t3 >= &0 /\ t1 + t2 + t3 = &1 /\ (x':real^3) = t1 % (x:real^3) + t2 % (v:real^3) + t3 % (w:real^3)` ASSUME_TAC THENL
        [EXISTS_TAC `t1:real` THEN EXISTS_TAC `t2:real` THEN EXISTS_TAC `t3:real` THEN ASM_MESON_TAC[];
         ASM_REWRITE_TAC[] THEN REPEAT (POP_ASSUM MP_TAC) THEN REPEAT STRIP_TAC THEN EXISTS_TAC `(t1:real)` THEN
         EXISTS_TAC `(t3:real)` THEN EXISTS_TAC `(t2:real)` THEN
         ASM_MESON_TAC[REAL_ARITH `(t1:real)+ (t3:real) +(t2:real)=t1 + t2 + t3`;VECTOR_ARITH ` t1 % x + t2 % v + t3 % w = (t1:real) % (x:real^3) + (t3:real) % (w:real^3) + (t2:real) % (v:real^3)`
]];
         STRIP_TAC THEN SUBGOAL_THEN `(x':real^3) - ((t1':real) % (x:real^3) + (t2':real) % (w:real^3) + (t3':real) % (v:real^3)) = vec 0` ASSUME_TAC THENL
             [POP_ASSUM MP_TAC THEN VECTOR_ARITH_TAC;
               POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
              REWRITE_TAC[VECTOR_ARITH `(t1 % x + t2 % v + t3 % w) - (t1' % x + t2' % w + t3' % v)= ((t1:real)- (t1':real)) % (x:real^3) +((t2:real)- (t3':real)) % (v:real^3)+((t3:real)-(t2':real)) % (w:real^3)`] THEN DISCH_TAC THEN
              SUBGOAL_THEN `(t2:real)-(t3':real)= &0` ASSUME_TAC THENL
                  [ASM_MESON_TAC[];
                   SUBGOAL_THEN `((t2:real) = (t3':real))` ASSUME_TAC THENL
                          [ASM_MESON_TAC[REAL_SUB_0];
                           SUBGOAL_THEN `(t2:real) >= &0` ASSUME_TAC THENL
                                [ASM_MESON_TAC[];
                                 EXISTS_TAC `(t1:real)` THEN EXISTS_TAC `(t2:real)` THEN EXISTS_TAC `t3:real` THEN
                                 ASM_MESON_TAC[]]]]]]);;


(*---------------------------------------------------------------------------------*)
(*     half_plane_norm_closed_fan    closed ({y:real^3| y $ 3 >= &0 /\ y $ 1 + y $ 2 + y $ 3 = &1})    *)
(*---------------------------------------------------------------------------------*)


let plane_norm_closed_fan=prove(`closed ({y:real^3| y $ 1+ y $ 2 + y $ 3 = &1})`,
 (let lemma= prove(`{y:real^3| vector [&1 ; &1 ; &1] dot y = &1}={y:real^3| y $ 1+ y $ 2 + y $ 3 = &1}`,
     ( let lem1=prove(`!a:real b:real c:real y:real^3. vector [a; b; c] dot y = a * (y $ 1) + b * (y $ 2) + c * (y $ 3)`, REPEAT GEN_TAC THEN REWRITE_TAC[dot; DIMINDEX_3;  SUM_3; VECTOR_3]) in 
REWRITE_TAC[lem1;  REAL_ARITH `&1 * (a:real)= a`]))  
  in
    SUBGOAL_THEN `{y:real^3| y $ 1+ y $ 2 + y $ 3 = &1}={y:real^3| vector [&1 ; &1 ; &1] dot y = &1}` ASSUME_TAC THENL
     [MESON_TAC[lemma];
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[CLOSED_HYPERPLANE]]));;




let halfspace_closed_fan=prove(`closed ({y:real^3| y $ 3 >= &0})`,
 (let lemma= prove(`{y:real^3| vector [&0 ; &0 ; &1] dot y >= &0}={y:real^3| y $ 3 >= &0}`,
     ( let lem1=prove(`!a:real b:real c:real y:real^3. vector [a; b; c] dot y = a * (y $ 1) + b * (y $ 2) + c * (y $ 3)`, REPEAT GEN_TAC THEN REWRITE_TAC[dot; DIMINDEX_3;  SUM_3; VECTOR_3]) in 
REWRITE_TAC[lem1; REAL_ARITH `&0 * (a:real)= &0`; REAL_ARITH `&0 + (a:real)= (a:real)`; REAL_ARITH `&1 * (a:real)= a`]))
  in
SUBGOAL_THEN `{y:real^3| y $ 3 >= &0}={y:real^3| vector [&0 ; &0 ; &1] dot y >= &0}` ASSUME_TAC
       THENL 
        [MESON_TAC[lemma];
        ASM_REWRITE_TAC[CLOSED_HALFSPACE_GE]]));;


let half_plane_norm_closed_fan=prove(`closed ({y:real^3| y $ 3 >= &0 /\ y $ 1 + y $ 2 + y $ 3 = &1})`,
SUBGOAL_THEN `{y:real^3| y $ 3 >= &0 /\ y $ 1 + y $ 2 + y $ 3 = &1}={y:real^3| y $ 3 >= &0} INTER {y:real^3|  y $ 1 + y $ 2 + y $ 3 = &1}` ASSUME_TAC THENL
 [REWRITE_TAC[INTER; IN_ELIM_THM];
  ASM_REWRITE_TAC[] THEN 
   ASM_MESON_TAC[plane_norm_closed_fan; halfspace_closed_fan; CLOSED_INTER]]);;

let halfspace_closed_fans=prove(`closed ({y:real^3| y $ 2 >= &0})`,
 (let lemma= prove(`{y:real^3| vector [&0 ; &1 ; &0] dot y >= &0}={y:real^3| y $ 2 >= &0}`,
     ( let lem1=prove(`!a:real b:real c:real y:real^3. vector [a; b; c] dot y = a * (y $ 1) + b * (y $ 2) + c * (y $ 3)`, REPEAT GEN_TAC THEN REWRITE_TAC[dot; DIMINDEX_3;  SUM_3; VECTOR_3]) in 
REWRITE_TAC[lem1; REAL_ARITH `&0 * (a:real)= &0`; REAL_ARITH `&0 + (a:real)= (a:real)`; REAL_ARITH ` (a:real)+ &0 = (a:real)`; REAL_ARITH `&1 * (a:real)= a`]))
  in
SUBGOAL_THEN `{y:real^3| y $ 2 >= &0}={y:real^3| vector [&0 ; &1 ; &0] dot y >= &0}` ASSUME_TAC
       THENL 
        [MESON_TAC[lemma];
        ASM_REWRITE_TAC[CLOSED_HALFSPACE_GE]]));;


let half_plane_norm_closed_fans=prove(`closed ({y:real^3| y $ 2 >= &0 /\ y $ 1 + y $ 2 + y $ 3 = &1})`,
SUBGOAL_THEN `{y:real^3| y $ 2 >= &0 /\ y $ 1 + y $ 2 + y $ 3 = &1}={y:real^3| y $ 2 >= &0} INTER {y:real^3|  y $ 1 + y $ 2 + y $ 3 = &1}` ASSUME_TAC THENL
 [REWRITE_TAC[INTER; IN_ELIM_THM];
  ASM_REWRITE_TAC[] THEN 
   ASM_MESON_TAC[plane_norm_closed_fan; halfspace_closed_fans; CLOSED_INTER]]);;


(*---------------------------------------------------------------------------------*)
(*    Property of  function_fan (x:real^3) (v:real^3) (w:real^3)= (\(y:real^3). y$1 % x + y$2 % v + y$3 % w  *)
(*---------------------------------------------------------------------------------*)



let function_fan= new_definition `function_fan (x:real^3) (v:real^3) (w:real^3)= (\(y:real^3). y$1 % x + y$2 % v + y$3 % w)`;;


let  linear_function_fan=prove(`!x:real^3 v:real^3 w:real^3. linear (function_fan x v w)`,
REWRITE_TAC[linear;function_fan; VECTOR_ADD_COMPONENT; VECTOR_ARITH `((a:real)+(b:real)) % (x:real^3)= a % x + b % x`;
VECTOR_ARITH `((a:real^3)+(b:real^3))+((c:real^3)+(d:real^3))+(e:real^3)+(f:real^3)= ((a:real^3)+(c:real^3)+(e:real^3))+(b:real^3)+(d:real^3)+(f:real^3)`; VECTOR_MUL_COMPONENT; VECTOR_ARITH `((a:real)*(b:real)) % (x:real^3)= a %( b % x)`] THEN
VECTOR_ARITH_TAC);;





let indepent_imp_injective=prove(`!x:real^3 v:real^3 w:real^3.
(!a:real b:real c:real. a % x + b % v + c % w = ((vec 0):real^3) ==> a = &0 /\ b = &0 /\ c = &0  )
==>
( !a:real^3 b:real^3. (function_fan x v w) (a) = (function_fan x v w) (b) ==> a = b)`,
(
let lemma=prove(`(a:real^3)$(i:num)- (b:real^3)$i =(a - b)$i`,MESON_TAC[VECTOR_SUB_COMPONENT])
in

REWRITE_TAC[function_fan] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
REWRITE_TAC[VECTOR_ARITH `((a:real^3)$1 % (x:real^3) + a$2 % (v:real^3) + a$3 % (w:real^3) = (b:real^3)$1 % x + b$2 % v + b$3 % w )<=> ((a$1 % x + a$2 % v + a$3 % w) - (b$1 % x + b$2 % v + b$3 % w )= ((vec 0):real^3))`;
VECTOR_ARITH `(((a:real^3)$1 % (x:real^3) + a$2 % (v:real^3) + a$3 % (w:real^3)) - ((b:real^3)$1 % x + b$2 % v + b$3 % w )=  ((vec 0):real^3)) <=> ((a$1 % x - b$1 % x)+(a$2 % v - b$2 % v)+(a$3 % w - b$3 % w)=  ((vec 0):real^3))`;
VECTOR_ARITH `(a:real) % (x:real^3)- (b:real) % (x:real^3)= (a - b) % x`] THEN DISCH_TAC THEN
SUBGOAL_THEN `((a:real^3)$1 - (b:real^3)$1) = &0 /\ (a$2 - b$2) = &0 /\ (a$3 - b$3) = &0` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN
    POP_ASSUM (MP_TAC o SPECL [`((a:real^3)$1 - (b:real^3)$1)`; `((a:real^3)$2 - (b:real^3)$2)`;`((a:real^3)$3 - (b:real^3)$3)`]) THEN MESON_TAC[TAUT `(p==>q)==>p==>q`];
    SUBGOAL_THEN `(a:real^3)-(b:real^3)= vec 0` ASSUME_TAC THENL
       [POP_ASSUM MP_TAC THEN REWRITE_TAC[ lemma] THEN REWRITE_TAC[CART_EQ;] THEN SIMP_TAC[vec;LAMBDA_BETA] THEN
        REWRITE_TAC[DIMINDEX_3;FORALL_3];
       ASM_MESON_TAC[VECTOR_SUB_EQ]]]));;



let image1_pass_function_fan=prove(`!x:real^3 v:real^3 w:real^3. 
IMAGE (function_fan x v w) {y:real^3| y $ 2 >= &0 /\ y $ 1 + y $ 2 + y $ 3 = &1}
= {y:real^3 | ?t1:real t2:real t3:real. (t2 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)}`,
REWRITE_TAC[IMAGE; function_fan; IN_ELIM_THM; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN EQ_TAC 
THENL
  [ REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN DISCH_TAC THEN 
   EXISTS_TAC `(x'':real^3)$1` THEN EXISTS_TAC `(x'':real^3)$2` THEN EXISTS_TAC `(x'':real^3)$3` THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   EXISTS_TAC `(vector [(t1:real); (t2:real); (t3:real)]):real^3` THEN REWRITE_TAC[VECTOR_3] THEN ASM_REWRITE_TAC[]]);;

let image2_pass_function_fan=prove(`!x:real^3 v:real^3 w:real^3. 
IMAGE (function_fan x v w) {y:real^3| y $ 3 >= &0 /\ y $ 1 + y $ 2 + y $ 3 = &1}
= {y:real^3 | ?t1:real t2:real t3:real. (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)}`,
REWRITE_TAC[IMAGE; function_fan; IN_ELIM_THM; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN EQ_TAC 
THENL
  [ REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN DISCH_TAC THEN 
   EXISTS_TAC `(x'':real^3)$1` THEN EXISTS_TAC `(x'':real^3)$2` THEN EXISTS_TAC `(x'':real^3)$3` THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   EXISTS_TAC `(vector [(t1:real); (t2:real); (t3:real)]):real^3` THEN REWRITE_TAC[VECTOR_3] THEN ASM_REWRITE_TAC[]]);;



(*---------------------------------------------------------------------------------*)
(*    closed (aff_ge {x, v} {w}) and closed (aff_ge {x} {v , w})  *)
(*---------------------------------------------------------------------------------*)




let closed_aff_ge_fan=prove(`(!x:real^3 v:real^3 w:real^3. aff_ge {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
==>
(!x:real^3 v:real^3 w:real^3. 
(!a:real b:real c:real. a % x + b % v + c % w = ((vec 0):real^3) ==> a = &0 /\ b = &0 /\ c = &0  )
==>
closed (aff_ge {x, v} {w}))`,
(let lemma=prove(`(a:real^3)$(i:num)- (b:real^3)$i =(a - b)$i`,MESON_TAC[VECTOR_SUB_COMPONENT])
in

DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
SUBGOAL_THEN `( !a:real^3 b:real^3. ((function_fan (x:real^3) (v:real^3) (w:real^3)):real^3->real^3) a = (function_fan x v w) b ==> a = b)` ASSUME_TAC THENL
  [ 
REWRITE_TAC[function_fan] THEN  REPEAT GEN_TAC THEN
REWRITE_TAC[VECTOR_ARITH `((a:real^3)$1 % (x:real^3) + a$2 % (v:real^3) + a$3 % (w:real^3) = (b:real^3)$1 % x + b$2 % v + b$3 % w )<=> ((a$1 % x + a$2 % v + a$3 % w) - (b$1 % x + b$2 % v + b$3 % w )= ((vec 0):real^3))`;
VECTOR_ARITH `(((a:real^3)$1 % (x:real^3) + a$2 % (v:real^3) + a$3 % (w:real^3)) - ((b:real^3)$1 % x + b$2 % v + b$3 % w )=  ((vec 0):real^3)) <=> ((a$1 % x - b$1 % x)+(a$2 % v - b$2 % v)+(a$3 % w - b$3 % w)=  ((vec 0):real^3))`;
VECTOR_ARITH `(a:real) % (x:real^3)- (b:real) % (x:real^3)= (a - b) % x`] THEN DISCH_TAC THEN
SUBGOAL_THEN `((a:real^3)$1 - (b:real^3)$1) = &0 /\ (a$2 - b$2) = &0 /\ (a$3 - b$3) = &0` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN
    POP_ASSUM (MP_TAC o SPECL [`((a:real^3)$1 - (b:real^3)$1)`; `((a:real^3)$2 - (b:real^3)$2)`;`((a:real^3)$3 - (b:real^3)$3)`]) THEN MESON_TAC[];
    SUBGOAL_THEN `(a:real^3)-(b:real^3)= vec 0` ASSUME_TAC THENL
       [POP_ASSUM MP_TAC THEN REWRITE_TAC[ lemma] THEN REWRITE_TAC[CART_EQ;] THEN SIMP_TAC[vec;LAMBDA_BETA] THEN
        REWRITE_TAC[DIMINDEX_3;FORALL_3];
       ASM_MESON_TAC[VECTOR_SUB_EQ]]];

SUBGOAL_THEN `linear ((function_fan (x:real^3) (v:real^3) (w:real^3)):real^3->real^3)` ASSUME_TAC THENL
   [MESON_TAC[linear_function_fan];
    ASSUME_TAC (half_plane_norm_closed_fan) THEN
     SUBGOAL_THEN `closed (IMAGE ((function_fan (x:real^3) (v:real^3) (w:real^3)):real^3->real^3) {y:real^3| y $ 3 >= &0 /\ y $ 1 + y $ 2 + y $ 3 = &1})` ASSUME_TAC THENL
        [ASM_MESON_TAC[CLOSED_INJECTIVE_LINEAR_IMAGE];
         POP_ASSUM MP_TAC THEN ASSUME_TAC(image2_pass_function_fan) THEN ASM_REWRITE_TAC[]]]]));;



let closed_aff_ge1_fan=prove(`
(!x:real^3 v:real^3 w:real^3. aff_ge {x} {v , w}={y:real^3 |  ?t1:real t2:real t3:real. (t2 >= &0)/\ (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)}) 
/\ 
(!x:real^3 v:real^3 w:real^3. aff_ge {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
==>
(!x:real^3 v:real^3 w:real^3. 
(!a:real b:real c:real. a % x + b % v + c % w = ((vec 0):real^3) ==> a = &0 /\ b = &0 /\ c = &0  )
==>
closed (aff_ge {x} {v, w}))`,
STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
SUBGOAL_THEN `(aff_ge {(x:real^3)} {(v:real^3) , (w:real^3)}) = (aff_ge {x , v} {w}) INTER (aff_ge {x , w} {v})` ASSUME_TAC
THENL
  [ASM_MESON_TAC[aff_ge_inter_aff_ge];
   SUBGOAL_THEN `closed (aff_ge {(x:real^3), (v:real^3)} {(w:real^3)})` ASSUME_TAC THENL
      [ASM_MESON_TAC[closed_aff_ge_fan]; 
       POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC  THEN
       SUBGOAL_THEN `!a:real c:real b:real. a % (x:real^3) + c % (w:real^3) + b % (v:real^3) = vec 0 ==> a = &0 /\ c = &0 /\ b = &0` ASSUME_TAC THENL
         [ASM_MESON_TAC[VECTOR_ARITH `((a:real) % (x:real^3) + (b:real) % (v:real^3) + (c:real) % (w:real^3)= vec 0)<=>((a:real) % (x:real^3)+ (c:real) % (w:real^3) + (b:real) % (v:real^3) = vec 0) `];
          REPEAT DISCH_TAC THEN 
          SUBGOAL_THEN `closed (aff_ge {(x:real^3), (w:real^3)} {(v:real^3)})` ASSUME_TAC THENL
            [ASM_MESON_TAC[closed_aff_ge_fan];
             ASM_MESON_TAC[CLOSED_INTER]]]]]);;

(*---------------------------------------------------------------------------------*)
(*    Property of  function1_fan (x:real^3) (v:real^3)= (\(y:real^2). y$1 % x + y$2 % v   *)
(*---------------------------------------------------------------------------------*)



let function1_fan= new_definition `function1_fan (x:real^3) (v:real^3) = (\(y:real^2). y$1 % x + y$2 % v)`;;

let  linear_function1_fan=prove(`!x:real^3 v:real^3. linear (function1_fan x v)`,
REWRITE_TAC[linear;function1_fan; VECTOR_ADD_COMPONENT;VECTOR_ARITH `((a:real)+(b:real)) % (x:real^3)= a % x + b % x`;
VECTOR_ARITH `((a:real^3)+(b:real^3))+((c:real^3)+(d:real^3))= ((a:real^3)+(c:real^3))+(b:real^3)+(d:real^3)`; VECTOR_MUL_COMPONENT; VECTOR_ARITH `((a:real)*(b:real)) % (x:real^3)= a %( b % x)`] THEN
VECTOR_ARITH_TAC);;



let indepent_imp_injective1=prove(`!x:real^3 v:real^3 w:real^3.
(!a:real b:real c:real. a % x + b % v = ((vec 0):real^3) ==> a = &0 /\ b = &0  )
==>
( !a:real^2 b:real^2. (function1_fan x v) (a) = (function1_fan x v) (b) ==> a = b)`,
(let lemma=prove(`(a:real^2)$(i:num)- (b:real^2)$i =(a - b)$i`,MESON_TAC[VECTOR_SUB_COMPONENT])
in
REWRITE_TAC[function1_fan] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
REWRITE_TAC[VECTOR_ARITH `((a:real^2)$1 % (x:real^3) + a$2 % (v:real^3) = (b:real^2)$1 % x + b$2 % v )<=> ((a$1 % x + a$2 % v ) - (b$1 % x + b$2 % v )= ((vec 0):real^3))`;
VECTOR_ARITH `(((a:real^2)$1 % (x:real^3) + a$2 % (v:real^3) ) - ((b:real^2)$1 % x + b$2 % v )=  ((vec 0):real^3)) <=> ((a$1 % x - b$1 % x)+(a$2 % v - b$2 % v)=  ((vec 0):real^3))`;
VECTOR_ARITH `(a:real) % (x:real^3)- (b:real) % (x:real^3)= (a - b) % x`] THEN DISCH_TAC THEN
SUBGOAL_THEN `((a:real^2)$1 - (b:real^2)$1) = &0 /\ (a$2 - b$2) = &0 ` ASSUME_TAC 
THENL  
    [POP_ASSUM MP_TAC THEN
    POP_ASSUM (MP_TAC o SPECL [`((a:real^2)$1 - (b:real^2)$1)`; `((a:real^2)$2 - (b:real^2)$2)`]) 
THEN MESON_TAC[TAUT `(p==>q)==>p==>q`];
    SUBGOAL_THEN `(a:real^2)-(b:real^2)= vec 0` ASSUME_TAC THENL
       [POP_ASSUM MP_TAC THEN REWRITE_TAC[ lemma] THEN REWRITE_TAC[CART_EQ;] THEN SIMP_TAC[vec;LAMBDA_BETA] THEN
        REWRITE_TAC[DIMINDEX_2;FORALL_2];
       ASM_MESON_TAC[VECTOR_SUB_EQ]]]));;



let image2_pass_function1_fan=prove(`!x:real^3 v:real^3. 
IMAGE (function1_fan x v) {y:real^2| y $ 2 >= &0 /\ y $ 1 + y $ 2  = &1}
= {y:real^3 | ?t1:real t2:real. (t2 >= &0) /\ (t1 + t2  = &1) /\ (y = t1 % x + t2 % v)}`,
REWRITE_TAC[IMAGE; function1_fan; IN_ELIM_THM; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN EQ_TAC
THENL
  [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN DISCH_TAC THEN 
   EXISTS_TAC `(x'':real^2)$1` THEN EXISTS_TAC `(x'':real^2)$2`  THEN ASM_REWRITE_TAC[];
   REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
   EXISTS_TAC `(vector [(t1:real); (t2:real)]):real^2` THEN REWRITE_TAC[VECTOR_2] THEN ASM_REWRITE_TAC[]]);;

(*--------------------------------------------------------------------------------------------*)
(*       closed_halfline_fan   closed  aff_ge {x} {v}                                         *)
(*--------------------------------------------------------------------------------------------*) 



let plane_norm_closed2_fan=prove(`closed ({y:real^2| y $ 1+ y $ 2 = &1})`,
(let lemma= prove(`{y:real^2| vector [&1 ; &1] dot y = &1}={y:real^2| y $ 1+ y $ 2 = &1}`,
     ( let lem1=prove(`!a:real b:real  y:real^2. vector [a; b] dot y = a * (y $ 1) + b * (y $ 2) `, REPEAT GEN_TAC THEN REWRITE_TAC[dot; DIMINDEX_2;  SUM_2; VECTOR_2]) in 
REWRITE_TAC[lem1;  REAL_ARITH `&1 * (a:real)= a`]))  
  in
    SUBGOAL_THEN `{y:real^2| y $ 1+ y $ 2 = &1}={y:real^2| vector [&1 ; &1] dot y = &1}` ASSUME_TAC THENL
     [MESON_TAC[lemma];
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[CLOSED_HYPERPLANE]]));;




let halfspace_closed2_fan=prove(`closed ({y:real^2| y $ 2 >= &0})`,
 (let lemma= prove(`{y:real^2| vector [ &0 ; &1] dot y >= &0}={y:real^2| y $ 2 >= &0}`,
     ( let lem1=prove(`!a:real b:real y:real^2. vector [a; b] dot y = a * (y $ 1) + b * (y $ 2)`, REPEAT GEN_TAC THEN REWRITE_TAC[dot; DIMINDEX_2;  SUM_2; VECTOR_2]) in 
REWRITE_TAC[lem1; REAL_ARITH `&0 * (a:real)= &0`; REAL_ARITH `&0 + (a:real)= (a:real)`; REAL_ARITH `&1 * (a:real)= a`]))
  in
SUBGOAL_THEN `{y:real^2| y $ 2 >= &0}={y:real^2| vector [ &0 ; &1] dot y >= &0}` ASSUME_TAC
       THENL 
        [MESON_TAC[lemma];
        ASM_REWRITE_TAC[CLOSED_HALFSPACE_GE]]));;


let half_plane_norm_closed2_fan=prove(`closed ({y:real^2| y $ 2 >= &0 /\ y $ 1 + y $ 2 = &1})`,
SUBGOAL_THEN `{y:real^2| y $ 2 >= &0 /\ y $ 1 + y $ 2 = &1}={y:real^2| y $ 2 >= &0} INTER {y:real^2|  y $ 1 + y $ 2  = &1}` ASSUME_TAC THENL
 [REWRITE_TAC[INTER; IN_ELIM_THM];
  ASM_REWRITE_TAC[] THEN 
   ASM_MESON_TAC[plane_norm_closed2_fan; halfspace_closed2_fan; CLOSED_INTER]]);;




let closed_halfline_fan=prove(`
(!x:real^3 v:real^3. aff_ge {x} {v} = {y:real^3 | ?t1:real t2:real. (t2 >= &0) /\ (t1 + t2 = &1) /\ (y = t1 % x + t2 % v )})
==>
(!x:real^3 v:real^3. 
(!a:real b:real. a % x + b % v = ((vec 0):real^3) ==> a = &0 /\ b = &0  )
==>
closed (aff_ge {x} { v}))`,
(
let lemma=prove(`(a:real^2)$(i:num)- (b:real^2)$i =(a - b)$i`,MESON_TAC[VECTOR_SUB_COMPONENT])
in 

DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
SUBGOAL_THEN `( !a:real^2 b:real^2. ((function1_fan (x:real^3) (v:real^3) ):real^2->real^3) a = (function1_fan x v) b ==> a = b)` ASSUME_TAC 
THENL
  [REWRITE_TAC[function1_fan] THEN  REPEAT GEN_TAC THEN
REWRITE_TAC[VECTOR_ARITH `((a:real^2)$1 % (x:real^3) + a$2 % (v:real^3) = (b:real^2)$1 % x + b$2 % v )<=> ((a$1 % x + a$2 % v ) - (b$1 % x + b$2 % v )= ((vec 0):real^3))`;
VECTOR_ARITH `(((a:real^2)$1 % (x:real^3) + a$2 % (v:real^3) ) - ((b:real^2)$1 % x + b$2 % v )=  ((vec 0):real^3)) <=> ((a$1 % x - b$1 % x)+(a$2 % v - b$2 % v)=  ((vec 0):real^3))`;
VECTOR_ARITH `(a:real) % (x:real^3)- (b:real) % (x:real^3)= (a - b) % x`] THEN DISCH_TAC THEN
SUBGOAL_THEN `((a:real^2)$1 - (b:real^2)$1) = &0 /\ (a$2 - b$2) = &0 ` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN
    POP_ASSUM (MP_TAC o SPECL [`((a:real^2)$1 - (b:real^2)$1)`; `((a:real^2)$2 - (b:real^2)$2)`]) THEN MESON_TAC[];
    SUBGOAL_THEN `(a:real^2)-(b:real^2)= vec 0` ASSUME_TAC THENL
       [POP_ASSUM MP_TAC THEN REWRITE_TAC[ lemma] THEN REWRITE_TAC[CART_EQ;] THEN SIMP_TAC[vec;LAMBDA_BETA] THEN
        REWRITE_TAC[DIMINDEX_2;FORALL_2];
       ASM_MESON_TAC[VECTOR_SUB_EQ]]];
  SUBGOAL_THEN `linear ((function1_fan (x:real^3) (v:real^3) ):real^2->real^3)` ASSUME_TAC THENL
   [MESON_TAC[linear_function1_fan];
    ASSUME_TAC (half_plane_norm_closed2_fan) THEN
     SUBGOAL_THEN `closed (IMAGE ((function1_fan (x:real^3) (v:real^3)):real^2->real^3) {y:real^2| y $ 2 >= &0 /\ y $ 1 + y $ 2 = &1})` ASSUME_TAC THENL
        [ASM_MESON_TAC[CLOSED_INJECTIVE_LINEAR_IMAGE];
         POP_ASSUM MP_TAC THEN ASSUME_TAC(image2_pass_function1_fan) THEN ASM_REWRITE_TAC[]]]]));;




(*--------------------------------------------------------------------------------------------*)
(*       The properties of      ballnorm_fan (x:real^3)={y:real^3 | dist(x,y) = &1}           *)
(*--------------------------------------------------------------------------------------------*) 





let ballnorm_fan=new_definition`ballnorm_fan (x:real^3)={y:real^3 | dist(x,y) = &1}`;;


let closed_ballnorm_fan=prove(`!x:real^3. closed (ballnorm_fan x)`,
GEN_TAC THEN REWRITE_TAC[ballnorm_fan] THEN
SUBGOAL_THEN  `{y:real^3 | dist((x:real^3),(y:real^3)) = &1} = frontier( ball((x:real^3), &1))` ASSUME_TAC
 THENL [ASSUME_TAC(REAL_ARITH `&0 < &1`) THEN POP_ASSUM MP_TAC THEN
        SIMP_TAC[frontier; CLOSURE_BALL; INTERIOR_OPEN; OPEN_BALL;
           REAL_LT_IMP_LE] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; IN_BALL; IN_CBALL] THEN
  REAL_ARITH_TAC;
   ASM_REWRITE_TAC[] THEN MESON_TAC[FRONTIER_CLOSED]]);;

let bounded_ballnorm_fan=prove(`!x:real^3 . bounded(ballnorm_fan x)`,
REPEAT GEN_TAC THEN REWRITE_TAC[ballnorm_fan;bounded] THEN
 EXISTS_TAC `norm(x:real^3) + &1`  THEN REWRITE_TAC[ dist; IN_ELIM_THM] 
  THEN GEN_TAC THEN STRIP_TAC THEN ASSUME_TAC(NORM_TRIANGLE_SUB) THEN
POP_ASSUM (MP_TAC o ISPECL [`(x':real^3)`; `(x:real^3)`]  o INST_TYPE [`:real^3`,`:real^3`])
  THEN REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[]);;

let bounded_ballnorm_fans=prove(`!x:real^3 v:real^3 w:real^3. bounded (aff_ge {x} {v, w} INTER ballnorm_fan x)`,
REPEAT GEN_TAC THEN ASSUME_TAC (bounded_ballnorm_fan) THEN
POP_ASSUM (MP_TAC o ISPEC `x:real^3`) THEN DISCH_TAC THEN
SUBGOAL_THEN `aff_ge {x} {(v:real^3), (w:real^3)} INTER ballnorm_fan x SUBSET ballnorm_fan (x:real^3)` ASSUME_TAC THENL
[SET_TAC[];
ASM_MESON_TAC[BOUNDED_SUBSET ]]);;



(*--------------------------------------------------------------------------------------------*)
(*       The properties of sets in norm ball                                                  *)
(*--------------------------------------------------------------------------------------------*) 



let closed_aff_ge_ballnorm_fan=prove(`
(!x:real^3 v:real^3 w:real^3. aff_ge {x} {v , w}={y:real^3 |  ?t1:real t2:real t3:real. (t2 >= &0)/\ (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)}) 
/\ 
(!x:real^3 v:real^3 w:real^3. aff_ge {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
==>
(!x:real^3 v:real^3 w:real^3. 
(!a:real b:real c:real. a % x + b % v + c % w = ((vec 0):real^3) ==> a = &0 /\ b = &0 /\ c = &0  )
==>
closed (aff_ge {x} {v, w} INTER ballnorm_fan x))`,
DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
SUBGOAL_THEN `closed (aff_ge {(x:real^3)} {(v:real^3), (w:real^3)})` ASSUME_TAC THENL
[ASM_MESON_TAC[ closed_aff_ge1_fan];
 ASSUME_TAC(closed_ballnorm_fan) THEN 
POP_ASSUM (MP_TAC o SPEC `x:real^3`) THEN DISCH_TAC THEN
ASM_MESON_TAC[CLOSED_INTER]]);;






let compact_aff_ge_ballnorm_fan=prove(`
(!x:real^3 v:real^3 w:real^3. aff_ge {x} {v , w}={y:real^3 |  ?t1:real t2:real t3:real. (t2 >= &0)/\ (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)}) 
/\ 
(!x:real^3 v:real^3 w:real^3. aff_ge {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
==>
(!x:real^3 v:real^3 w:real^3. 
(!a:real b:real c:real. a % x + b % v + c % w = ((vec 0):real^3) ==> a = &0 /\ b = &0 /\ c = &0  )
==>
compact (aff_ge {x} {v, w} INTER ballnorm_fan x))`,
DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
SUBGOAL_THEN `closed (aff_ge {x} {v, w} INTER ballnorm_fan x)` ASSUME_TAC 
THENL
  [ASM_MESON_TAC[closed_aff_ge_ballnorm_fan];
    ASSUME_TAC(bounded_ballnorm_fans) 
    THEN
   POP_ASSUM (MP_TAC o ISPECL [`x:real^3`; `v:real^3`; `w:real^3`]) THEN
    ASM_MESON_TAC[BOUNDED_CLOSED_IMP_COMPACT ]]);;




let vectornorm_fan=new_definition`vectornorm_fan x v =(inv (norm (v - x))) % (v - x)`;;  

(*g`(!x:real^3 v:real^3. aff_ge {x} {v} = {y:real^3 | ?t1:real t2:real. (t2 >= &0) /\ (t1 + t2 = &1) /\ (y = t1 % x + t2 % v )})
==>
(!x:real^3 v:real^3. 
(!a:real b:real. a % x + b % v = ((vec 0):real^3) ==> a = &0 /\ b = &0  )
==>
aff_ge {x} {v} INTER ballnorm_fan x = {vectornorm_fan x v})`;;

e(DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; INTER; ballnorm_fan; vectornorm_fan; IN_ELIM_THM; IN_SING] THEN GEN_TAC THEN EQ_TAC);;*)



let closed_point_fan=prove(`
(!x:real^3 v:real^3. aff_ge {x} {v} = {y:real^3 | ?t1:real t2:real. (t2 >= &0) /\ (t1 + t2 = &1) /\ (y = t1 % x + t2 % v )})
==>

(!x:real^3 v:real^3. 
(!a:real b:real. a % x + b % v = ((vec 0):real^3) ==> a = &0 /\ b = &0  )
==>
closed (aff_ge {x} {v} INTER ballnorm_fan x) )`,
DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
SUBGOAL_THEN `closed (aff_ge {(x:real^3)} {(v:real^3)})` ASSUME_TAC THENL
   [ASM_MESON_TAC[ closed_halfline_fan]; 
    SUBGOAL_THEN `closed (ballnorm_fan (x:real^3))` ASSUME_TAC THENL
       [ASM_MESON_TAC[closed_ballnorm_fan];
        ASM_MESON_TAC[CLOSED_INTER]]]);;









let w_darts_in_ball=new_definition`w_darts_in_ball  (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) (h:real) = (ballnorm_fan x) INTER (wedge5_fan x V E v u i h)`;;


let subset_of_indepent_is_indepent_fan=prove(`
!x:real^3 v:real^3 w:real^3.
(!a:real b:real c:real. a % x + b % v + c % w = ((vec 0):real^3) ==> a = &0 /\ b = &0 /\ c = &0  )
==>(!a:real b:real. a % x + b % v  = ((vec 0):real^3) ==> a = &0 /\ b = &0  )`,
REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN POP_ASSUM (MP_TAC o SPECL [`a:real`; `b:real`;`&0`]) THEN REWRITE_TAC[VECTOR_ARITH `&0 % (w:real^3)= vec 0`; VECTOR_ARITH `(a:real^3) + vec 0 = a`]);;




let exist_fan=prove(`
(!x:real^3 v:real^3. aff_ge {x} {v} = {y:real^3 | ?t1:real t2:real. (t2 >= &0) /\ (t1 + t2 = &1) /\ (y = t1 % x + t2 % v )})
/\
(!x:real^3 v:real^3 w:real^3. aff_ge {x} {v , w}={y:real^3 |  ?t1:real t2:real t3:real. (t2 >= &0)/\ (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)}) 
/\ 
(!x:real^3 v:real^3 w:real^3. aff_ge {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})

==>
(!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (v1:real^3) (w1:real^3) (i:num).
(!a:real b:real c:real. a % x + b % v + c % w = ((vec 0):real^3) ==> a = &0 /\ b = &0 /\ c = &0  )
/\ (!a:real b:real c:real. a % x + b % v1 + c % w1 = ((vec 0):real^3) ==> a = &0 /\ b = &0 /\ c = &0  )
/\
aff_ge {x} {v} INTER aff_ge {x} {v1, w1} INTER ballnorm_fan x ={}
==>

?h:real.
(h > &0)
/\ 
(!y1:real^3 y2:real^3. (y1 IN aff_ge {x} {v} INTER ballnorm_fan x) /\ y2 IN (aff_ge {x} {v1, w1} INTER ballnorm_fan x)
==> h  <= dist(y1,y2) ))`,
DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT (POP_ASSUM MP_TAC) THEN 
DISCH_THEN(LABEL_TAC "a") THEN
DISCH_THEN(LABEL_TAC "b") THEN
DISCH_THEN(LABEL_TAC "c") 
THEN DISCH_THEN(LABEL_TAC "d") THEN
 SUBGOAL_THEN `(!a:real b:real. a % x + b % v  = ((vec 0):real^3) ==> a = &0 /\ b = &0  )` ASSUME_TAC THENL
   [USE_THEN "b" MP_TAC
     THEN  DISCH_TAC THEN REPEAT GEN_TAC THEN POP_ASSUM (MP_TAC o SPECL [`a:real`; `b:real`;`&0`]) THEN REWRITE_TAC[VECTOR_ARITH `&0 % (w:real^3)= vec 0`; VECTOR_ARITH `(a:real^3) + vec 0 = a`];
    SUBGOAL_THEN `closed (aff_ge {(x:real^3)} {(v:real^3)} INTER ballnorm_fan x)` ASSUME_TAC 
THENL
      [ASM_MESON_TAC[ closed_point_fan];
       SUBGOAL_THEN `compact (aff_ge {(x:real^3)} {(v1:real^3), (w1:real^3)} INTER ballnorm_fan x)` ASSUME_TAC THENL
          [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] compact_aff_ge_ballnorm_fan) THEN ASM_REWRITE_TAC[];
           SUBGOAL_THEN `(aff_ge {(x:real^3)} {v:real^3} INTER ballnorm_fan x) INTER (aff_ge {x} {(v1:real^3),(w1:real^3)} INTER ballnorm_fan x)={}` ASSUME_TAC THENL
             [USE_THEN "d" MP_TAC  THEN SET_TAC[];              
              POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN MP_TAC( ISPECL [`aff_ge {(x:real^3)} {(v:real^3)} INTER ballnorm_fan x`;  `aff_ge {(x:real^3)} {(v1:real^3), (w1:real^3)} INTER ballnorm_fan x`] SEPARATE_CLOSED_COMPACT) THEN MESON_TAC[REAL_ARITH `(&0 < (d:real)) <=> (d > &0)`]]]]]);;

let ballsets_fan=new_definition`ballsets_fan (s:real^3->bool) (h:real)= {y:real^3| ?x:real^3. dist(x,y) < h /\ x IN s} `;;


let exists_ballsets_fan =prove(`
(!x:real^3 v:real^3. aff_ge {x} {v} = {y:real^3 | ?t1:real t2:real. (t2 >= &0) /\ (t1 + t2 = &1) /\ (y = t1 % x + t2 % v )})
/\
(!x:real^3 v:real^3 w:real^3. aff_ge {x} {v , w}={y:real^3 |  ?t1:real t2:real t3:real. (t2 >= &0)/\ (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)}) 
/\ 
(!x:real^3 v:real^3 w:real^3. aff_ge {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})

==>
(!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (v1:real^3) (w1:real^3) (i:num).
(!a:real b:real c:real. a % x + b % v + c % w = ((vec 0):real^3) ==> a = &0 /\ b = &0 /\ c = &0  )
/\ (!a:real b:real c:real. a % x + b % v1 + c % w1 = ((vec 0):real^3) ==> a = &0 /\ b = &0 /\ c = &0  )
/\
aff_ge {x} {v} INTER aff_ge {x} {v1, w1} INTER ballnorm_fan x ={}
==>

?h:real.
(h > &0)
/\ (ballsets_fan (aff_ge {x} {v} INTER ballnorm_fan x) h INTER (aff_ge {x} {v1, w1} INTER ballnorm_fan x) = {})
)`,
DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
SUBGOAL_THEN `?h:real.
(h > &0)
/\ 
(!y1:real^3 y2:real^3. (y1 IN aff_ge {x} {v} INTER ballnorm_fan x) /\ y2 IN (aff_ge {x} {v1, w1} INTER ballnorm_fan x)
==> h  <= dist(y1,y2) )` ASSUME_TAC THENL
 [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] exist_fan) THEN ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ballsets_fan;INTER;EXTENSION ; EMPTY;IN_ELIM_THM; ] THEN STRIP_TAC THENL 
     [ASM_REWRITE_TAC[];
      GEN_TAC THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN 
      POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM (MP_TAC o SPECL [`x'':real^3`;`x':real^3`]) THEN
      DISCH_THEN(LABEL_TAC "a") THEN DISCH_THEN(LABEL_TAC "b") THEN DISCH_THEN(LABEL_TAC "c") 
      THEN DISCH_THEN(LABEL_TAC "d") THEN DISCH_THEN(LABEL_TAC "e") THEN DISCH_THEN(LABEL_TAC "f") THEN
      USE_THEN "a" MP_TAC THEN ANTS_TAC THENL
           [USE_THEN "c" MP_TAC THEN USE_THEN "d" MP_TAC THEN USE_THEN "e" MP_TAC THEN USE_THEN "f" MP_TAC
              THEN REWRITE_TAC[INTER;IN_ELIM_THM;INSERT;IN_ELIM_THM] THEN SET_TAC[];
            USE_THEN "b" MP_TAC THEN REAL_ARITH_TAC]]]);;




(*-------------------------------------------------------------------------------------------*)
(* cone_ge_fan_inter_aff_ge_is_empty                                                         *)
(*-------------------------------------------------------------------------------------------*)



let cone_ge_fan=new_definition`cone_ge_fan (x:real^3) (s:real^3->bool)= {y:real^3| ?a:real z:real^3. (&0 <= a)/\(z IN s) /\ (y =a % (z - x) + x)}`;;



let cone_ge_fan_inter_aff_ge_is_empty=prove(`
(!x:real^3 v:real^3. aff_ge {x} {v} = {y:real^3 | ?t1:real t2:real. (t2 >= &0) /\ (t1 + t2 = &1) /\ (y = t1 % x + t2 % v )})
/\
(!x:real^3 v:real^3 w:real^3. aff_ge {x} {v , w}={y:real^3 |  ?t1:real t2:real t3:real. (t2 >= &0)/\ (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)}) 
/\ 
(!x:real^3 v:real^3 w:real^3. aff_ge {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})

==>
(!(x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (v1:real^3) (w1:real^3) (i:num).
(!a:real b:real c:real. a % x + b % v + c % w = ((vec 0):real^3) ==> a = &0 /\ b = &0 /\ c = &0  )
/\ (!a:real b:real c:real. a % x + b % v1 + c % w1 = ((vec 0):real^3) ==> a = &0 /\ b = &0 /\ c = &0  )
/\
aff_ge {x} {v} INTER aff_ge {x} {v1, w1} INTER ballnorm_fan x ={}
/\ ~(v = x)
==>

?h:real.
(h > &0)
/\ (cone_ge_fan x ((ballsets_fan (aff_ge {x} {v} INTER ballnorm_fan x) h)INTER ballnorm_fan x ) INTER aff_ge {x} {v1, w1} = {x})
)`,
DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC 

THEN SUBGOAL_THEN `
?h:real.
(h > &0)
/\ ballsets_fan (aff_ge {(x:real^3)} {(v:real^3)} INTER ballnorm_fan x) h INTER (aff_ge {x} {(v1:real^3), (w1:real^3)} INTER ballnorm_fan x) = {}
` ASSUME_TAC
THENL (*1*)[MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]  exists_ballsets_fan) THEN ASM_REWRITE_TAC[];(*1*)
           POP_ASSUM MP_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THENL
            (*2*)[ASM_REWRITE_TAC[];(*2*)
                  REWRITE_TAC [cone_ge_fan; EXTENSION; IN_SING; INTER; IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL
                    (*3*)[ASM_CASES_TAC `(x':real^3)=(x:real^3)` THENL
                            (*4*)[ASM_REWRITE_TAC[]; (*4*)
                                 MP_TAC (ISPECL [`x':real^3`; `x:real^3`] imp_norm_not_zero_fan) 
                                   THEN DISCH_TAC
				   THEN SUBGOAL_THEN `~(norm((x':real^3)-(x:real^3))= &0)` ASSUME_TAC THENL
                                      (*5*)[SET_TAC[];(*5*)
					    POP_ASSUM MP_TAC THEN  DISCH_THEN(LABEL_TAC "a")
					      THEN REPEAT STRIP_TAC 
					      THEN ASM_REWRITE_TAC[]
					      THEN ABBREV_TAC `(x1:real^3)= inv (norm ((x':real^3)-(x:real^3))) % (x'-x) + x`
					      THEN SUBGOAL_THEN `(x1:real^3) IN ballnorm_fan (x:real^3)` ASSUME_TAC THENL
					        (*6*)[REWRITE_TAC[ballnorm_fan; IN_ELIM_THM] 
							THEN EXPAND_TAC "x1"
							THEN REWRITE_TAC[dist]
							THEN REWRITE_TAC[VECTOR_ARITH `(x:real^3)-((a:real^3)+(x:real^3))= --(a)`; VECTOR_ARITH `-- ((a:real)% (v:real^3))=(-- a) % v`; NORM_MUL;REAL_ABS_NEG; REAL_ABS_INV; REAL_ABS_NORM]
							THEN USE_THEN "a"  MP_TAC
							THEN MP_TAC(ISPEC `norm ((x':real^3)-(x:real^3))` REAL_MUL_LINV)
							THEN MESON_TAC[]; (*6*)
						      SUBGOAL_THEN `(x1:real^3) IN aff_ge {(x:real^3)} {(v1:real^3),(w1:real^3)}` ASSUME_TAC
							THENL (*7*)[ POP_ASSUM MP_TAC
							THEN POP_ASSUM MP_TAC
							THEN POP_ASSUM MP_TAC
							THEN POP_ASSUM MP_TAC
							THEN ASM_REWRITE_TAC[]
							THEN DISCH_THEN (LABEL_TAC "b")
							THEN DISCH_THEN (LABEL_TAC "C")
							THEN DISCH_THEN (LABEL_TAC "D") 
							THEN DISCH_THEN (LABEL_TAC "E")
							THEN REMOVE_THEN "C" MP_TAC
							THEN REWRITE_TAC[IN_ELIM_THM]
							THEN STRIP_TAC
							THEN EXISTS_TAC `&1 - inv (norm((x':real^3)-(x:real^3))) + inv (norm (x' - x)) * (t1:real) `
							THEN EXISTS_TAC `inv (norm((x':real^3)-(x:real^3))) * (t2:real) `
							THEN EXISTS_TAC `inv (norm((x':real^3)-(x:real^3))) * (t3:real) `
							THEN EXPAND_TAC "x1"
							THEN REWRITE_TAC[VECTOR_ARITH`((a:real)-(b:real)+(c:real))%(v:real^3)=(a:real) % v -(b:real)% v+(c:real) %(v:real^3)`;
VECTOR_ARITH `&1 % (x:real^3)=x`; VECTOR_ARITH `((a:real)*(b:real)) % (v:real^3)= (a % (b % v))`;
VECTOR_ARITH `(x - inv (norm (x' - x)) % x + inv (norm (x' - x)) % t1 % x) +
 inv (norm (x' - x)) % t2 % v1 +
 inv (norm (x' - x)) % t3 % w1 =(inv (norm ((x':real^3)- x))) % ( t1 % x + t2 % v1+ t3% w1 -x)+ (x:real^3)` 

]
							THEN STRIP_TAC 
							THENL [SUBGOAL_THEN `&0 <= inv (norm ((x':real^3)-(x:real^3))) ` ASSUME_TAC 
                                                                   THENL [MATCH_MP_TAC REAL_LE_INV 
										 THEN MESON_TAC[NORM_POS_LE];
									       ASM_MESON_TAC[REAL_LE_MUL; REAL_ARITH `(a:real)>= &0 <=> &0 <= a`]];
								    STRIP_TAC THENL [SUBGOAL_THEN `&0 <= inv (norm ((x':real^3)-(x:real^3))) ` ASSUME_TAC
											    THENL [MATCH_MP_TAC REAL_LE_INV
													  THEN MESON_TAC[NORM_POS_LE];
													ASM_MESON_TAC[REAL_LE_MUL; REAL_ARITH `(a:real)>= &0 <=> &0 <= a`]];
											  REWRITE_TAC[REAL_ARITH `(&1 - inv (norm (x' - x)) + inv (norm (x' - x)) * t1) +
 inv (norm (x' - x)) * t2 +
 inv (norm (x' - x)) * t3= &1 - inv (norm (x' - x)) + inv (norm (x' - x)) * (t1 + t2 + t3)`]
											    THEN STRIP_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_ARITH `(a:real) * &1 = a`; REAL_ARITH `&1 - (a:real) +(a:real) = &1`];
															SUBGOAL_THEN `(x':real^3) -(x:real^3)= (t1:real) % (x:real^3) + (t2:real) % (v1:real^3) + (t3:real) % (w1:real^3) -(x:real^3)` ASSUME_TAC
												THENL [POP_ASSUM MP_TAC THEN VECTOR_ARITH_TAC;
													     SUBGOAL_THEN `inv (norm   ((x':real^3) -(x:real^3)) )  % ((x':real^3) -(x:real^3)) = inv (norm   ((x':real^3) -(x:real^3)) ) % ((t1:real) % (x:real^3) + (t2:real) % (v1:real^3) + (t3:real) % (w1:real^3) -(x:real^3))` ASSUME_TAC
												    THENL [ASM_MESON_TAC[ VECTOR_MUL_LCANCEL ];
													   ASM_MESON_TAC[]]]]]]; (*7*)
								     SUBGOAL_THEN `(x1:real^3) IN ballsets_fan (aff_ge {(x:real^3)} {(v:real^3)} INTER ballnorm_fan x) (h:real)` ASSUME_TAC 
								       THENL (*8*) [POP_ASSUM MP_TAC
										      THEN POP_ASSUM MP_TAC
										      THEN POP_ASSUM MP_TAC
										      THEN POP_ASSUM MP_TAC
										      THEN POP_ASSUM MP_TAC
										      THEN POP_ASSUM MP_TAC
										      THEN POP_ASSUM MP_TAC 
										      THEN POP_ASSUM MP_TAC
										      THEN DISCH_THEN (LABEL_TAC "b")
										      THEN DISCH_THEN (LABEL_TAC "c")
										      THEN DISCH_THEN (LABEL_TAC "d")
										      THEN DISCH_THEN (LABEL_TAC "e")
										      THEN DISCH_THEN (LABEL_TAC "f")
										      THEN DISCH_THEN (LABEL_TAC "g")
										      THEN DISCH_THEN (LABEL_TAC "h")
										      THEN DISCH_THEN (LABEL_TAC "i")
										      THEN SUBGOAL_THEN `norm ((z:real^3)-(x:real^3))= &1` ASSUME_TAC 
									              THENL (*9*)[REMOVE_THEN "d" MP_TAC 
												    THEN REWRITE_TAC[ballnorm_fan; IN_ELIM_THM; dist; NORM_SUB];(*9*)
												  POP_ASSUM MP_TAC 
												    THEN DISCH_THEN (LABEL_TAC "k")
												    THEN SUBGOAL_THEN `(x':real^3)- (x:real^3)= (a:real) % ((z:real^3)-x )` ASSUME_TAC
											  THENL (*10*)[REMOVE_THEN "e" MP_TAC THEN VECTOR_ARITH_TAC;(*10*)
												       POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "l")
													 THEN SUBGOAL_THEN `norm((x':real^3)- (x:real^3))= norm((a:real) % ((z:real^3)-x ))` ASSUME_TAC
											      THENL (*11*)[SET_TAC[]; (*11*)
													   POP_ASSUM MP_TAC THEN DISCH_THEN (LABEL_TAC "m") 
													     THEN SUBGOAL_THEN `norm((x':real^3)- (x:real^3))= abs (a:real) * norm((z:real^3)-x )` ASSUME_TAC
												  THENL (*12*)[POP_ASSUM MP_TAC 
														 THEN REWRITE_TAC[NORM_MUL];(*12*)
													       POP_ASSUM MP_TAC 
														 THEN USE_THEN "k" (fun th -> REWRITE_TAC[th]) 
														 THEN REWRITE_TAC[REAL_ARITH `(a:real)* &1 = a`]
														 THEN SUBGOAL_THEN `abs (a:real)=a`ASSUME_TAC 
												      THENL (*13*)[USE_THEN "b" MP_TAC THEN REAL_ARITH_TAC;(*13*)
														   POP_ASSUM (fun th-> REWRITE_TAC[th]) 
														     THEN DISCH_THEN (LABEL_TAC "n")
														     THEN REMOVE_THEN "l" MP_TAC
														     THEN USE_THEN "n" (fun th-> REWRITE_TAC[SYM th])
														     THEN DISCH_THEN (LABEL_TAC "l")
														     THEN SUBGOAL_THEN `(inv (norm (x'- x))) % ((x':real^3)- (x:real^3)) = (inv (norm (x' - x))) % (norm (x' - x) % ((z:real^3)- x ))` ASSUME_TAC
													  THENL (*14*)[POP_ASSUM MP_TAC THEN MESON_TAC[];(*14*)
														       POP_ASSUM MP_TAC 
															 THEN REWRITE_TAC[VECTOR_ARITH `(a:real)%(b:real)%(v:real^3)=(a*b)%v`] 
															 THEN USE_THEN "a" (fun th-> MP_TAC(ISPEC `norm((x':real^3)-(x:real^3))` REAL_MUL_LINV) THEN  REWRITE_TAC[th] )
															 THEN DISCH_TAC THEN POP_ASSUM (fun th -> REWRITE_TAC[th])
															 THEN REWRITE_TAC[VECTOR_ARITH `&1%(v:real^3)=v`; VECTOR_ARITH `((a:real^3)=(z:real^3)-(x:real^3))<=>(a+x=z)`]
															 THEN USE_THEN "g" (fun th-> REWRITE_TAC[th])
															 THEN DISCH_TAC THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
															 THEN REWRITE_TAC[INTER] 
															 THEN ASM_REWRITE_TAC[] (*14*)] (*13*)] (*12*)] (*11*)] (*10*)] (*9*)]; (*8*)
										    SUBGOAL_THEN `x1 IN ballsets_fan (aff_ge {(x:real^3)} {(v:real^3)} INTER ballnorm_fan x) h INTER (aff_ge {x} {(v1:real^3), (w1:real^3)} INTER ballnorm_fan x)` ASSUME_TAC
										      THENL (*9*)[SET_TAC[];(*9*)
												  SET_TAC[]](*9*) (*8*)] (*7*)] (*6*)] (*5*)] (*4*)]; (*3*)

			  DISCH_TAC
			    THEN POP_ASSUM (fun th-> REWRITE_TAC[th])
			    THEN STRIP_TAC
			    THENL(*4*) [EXISTS_TAC `&0`
					  THEN EXISTS_TAC `inv(norm((v:real^3)-(x:real^3))) % (v-x)+x`
					  THEN STRIP_TAC
					  THENL (*5*)[REAL_ARITH_TAC;(*5*)
						      REPEAT STRIP_TAC	
								       THENL (*7*)[REWRITE_TAC[ballsets_fan; IN_ELIM_THM]
										     THEN EXISTS_TAC `inv(norm((v:real^3)-(x:real^3))) % (v-x)+x` 
										     THEN REWRITE_TAC[dist; VECTOR_ARITH `(v:real^3)-v= vec 0`; NORM_0]
										     THEN STRIP_TAC
										     THENL (*8*)[SET_TAC[REAL_ARITH `&0 <(h:real) <=> h > &0`];(*8*)
												 STRIP_TAC THENL (*9*)[ASM_REWRITE_TAC[]
															 THEN REWRITE_TAC[IN_ELIM_THM]
															 THEN EXISTS_TAC `&1 - inv (norm ((v:real^3)-(x:real^3)))`
															 THEN EXISTS_TAC `inv (norm ((v:real^3)-(x:real^3)))`
															 THEN STRIP_TAC THENL(*10*) [ ASM_MESON_TAC[imp_norm_ge_zero_fan]; (*10*)
																		      STRIP_TAC THENL (*11*)[REAL_ARITH_TAC;(*11*)
																					     REWRITE_TAC[VECTOR_ARITH `(a:real) % ((v:real^3)-(x:real^3))+(x:real^3)= a % v - a % x + x`; VECTOR_ARITH `(a:real) % (v:real^3)- a % (x:real^3)+(x:real^3)= (&1 - a) % x + a % v`](*11*)] (*10*)]; (*9*)
														       REWRITE_TAC[ballnorm_fan; IN_ELIM_THM; dist; VECTOR_ARITH `(x:real^3)-((a:real^3)+(x:real^3))= --a`; NORM_NEG; NORM_MUL ]
															 THEN SUBGOAL_THEN `inv(norm((v:real^3)-(x:real^3))) > &0 ` ASSUME_TAC
															 THENL (*10*)[ASM_MESON_TAC[imp_norm_gl_zero_fan];(*10*)
																      SUBGOAL_THEN `abs(inv(norm((v:real^3)-(x:real^3))))=inv(norm((v:real^3)-(x:real^3)))` ASSUME_TAC 
															     THENL (*11*)[ASM_REWRITE_TAC[REAL_ABS_REFL] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;(*11*)
																	  POP_ASSUM (fun th -> REWRITE_TAC[th]) THEN SUBGOAL_THEN `~ (norm ((v:real^3)-(x:real^3))= &0)` ASSUME_TAC
																	    THENL (*12*)[SET_TAC[imp_norm_not_zero_fan];(*12*)
																			 POP_ASSUM MP_TAC THEN MESON_TAC[REAL_MUL_RINV;REAL_MUL_SYM](*12*)] (*11*)] (*10*)] (*9*)] (*8*)]; (*7*)

										   REWRITE_TAC[ballnorm_fan; IN_ELIM_THM; dist; VECTOR_ARITH `(x:real^3)-((a:real^3)+(x:real^3))= --a`; NORM_NEG; NORM_MUL ] 
										     THEN SUBGOAL_THEN `inv(norm((v:real^3)-(x:real^3))) > &0 ` ASSUME_TAC 
										     THENL (*8*)[SET_TAC[imp_norm_gl_zero_fan];(*8*)
												 SUBGOAL_THEN `abs(inv(norm((v:real^3)-(x:real^3))))=inv(norm((v:real^3)-(x:real^3)))` ASSUME_TAC
											 THENL (*9*)[ASM_REWRITE_TAC[REAL_ABS_REFL] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;(*9*)
								     POP_ASSUM (fun th -> REWRITE_TAC[th]) 
								       THEN SUBGOAL_THEN `~ (norm ((v:real^3)-(x:real^3))= &0)` ASSUME_TAC
								       THENL (*10*)[ASM_MESON_TAC[imp_norm_not_zero_fan];(*10*)
										   POP_ASSUM MP_TAC 
										     THEN MESON_TAC[REAL_MUL_RINV;REAL_MUL_SYM](*10*)] (*9*)](*8*)];(*7*) 
					REWRITE_TAC[VECTOR_ARITH `&0 % (v:real^3)= vec 0`; VECTOR_ARITH `vec 0 + (x:real^3)=x`](*7*)](*5*)];(*4*)


ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `&1` THEN EXISTS_TAC `&0` THEN EXISTS_TAC `&0`
  THEN STRIP_TAC THENL [REAL_ARITH_TAC; STRIP_TAC THENL [REAL_ARITH_TAC; STRIP_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]]]]]]] );;





let proj_fan=new_definition`proj_fan (x:real^3) = \y:real^3. inv(norm(y - x)) % (y - x )`;; 


let proj_injective_fan=prove(`!x:real^3 v:real^3 w:real^3. (proj_fan (x) (v) = proj_fan (x) (w:real^3)) /\ (norm (v - x) = norm (w - x)) <=> (v = w)`,
REPEAT GEN_TAC THEN EQ_TAC
 THENL 
 [REWRITE_TAC[proj_fan] THEN ASM_CASES_TAC `(v:real^3) = (x:real^3)` 

THENL
   [SUBGOAL_THEN `(v:real^3) - (x:real^3)=vec 0` ASSUME_TAC THENL
       [POP_ASSUM MP_TAC THEN VECTOR_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN SUBGOAL_THEN `(w:real^3)- (x:real^3)=vec 0` ASSUME_TAC THENL
            [POP_ASSUM MP_TAC THEN REWRITE_TAC[NORM_0] THEN MESON_TAC[NORM_EQ_0];
            POP_ASSUM MP_TAC THEN VECTOR_ARITH_TAC]];

       ASM_CASES_TAC `(w:real^3) = (x:real^3)` THENL 
        [SUBGOAL_THEN `(w:real^3) - (x:real^3)=vec 0` ASSUME_TAC THENL
            [POP_ASSUM MP_TAC THEN VECTOR_ARITH_TAC;
             ASM_REWRITE_TAC[] THEN STRIP_TAC THEN SUBGOAL_THEN `(v:real^3)- (x:real^3)=vec 0` ASSUME_TAC THENL
                [POP_ASSUM MP_TAC THEN REWRITE_TAC[NORM_0] THEN MESON_TAC[NORM_EQ_0];
                SUBGOAL_THEN `(v:real^3)=(x:real^3)`ASSUME_TAC THENL
                    [POP_ASSUM MP_TAC THEN VECTOR_ARITH_TAC;
                     SET_TAC[]]]];
        STRIP_TAC THEN 
        SUBGOAL_THEN `norm((v:real^3)-(x:real^3))% inv (norm (v - x)) % (v - x) =norm(v-x)% inv (norm ((w:real^3) - x)) % (w - x)`ASSUME_TAC THENL
          [ SET_TAC[];
            POP_ASSUM MP_TAC THEN REWRITE_TAC[VECTOR_ARITH `(a:real)%(b:real)%(c:real^3)=(a * b) % c` ]
              THEN SUBGOAL_THEN `~(norm ((v:real^3)-(x:real^3)) = &0)` ASSUME_TAC THENL
               [STRIP_TAC THEN SUBGOAL_THEN `(v:real^3)-(x:real^3)= vec 0` ASSUME_TAC THENL
                   [POP_ASSUM MP_TAC THEN MESON_TAC[NORM_EQ_0];
                    SUBGOAL_THEN `(v:real^3) = (x:real^3)` ASSUME_TAC THENL
                     [POP_ASSUM MP_TAC THEN VECTOR_ARITH_TAC;
                     SET_TAC[]]];
               SUBGOAL_THEN `(norm ((v:real^3) - (x:real^3)) * inv (norm (v - x)))= &1` ASSUME_TAC THENL
                  [POP_ASSUM MP_TAC THEN MP_TAC(ISPEC `norm ((v:real^3)-(x:real^3))` REAL_MUL_RINV) THEN MESON_TAC[];
                  ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `~(norm ((w:real^3)-(x:real^3)) = &0)` ASSUME_TAC THENL
                     [STRIP_TAC THEN SUBGOAL_THEN `(w:real^3)-(x:real^3)= vec 0` ASSUME_TAC THENL
                          [POP_ASSUM MP_TAC THEN MESON_TAC[NORM_EQ_0];
                           SUBGOAL_THEN `(w:real^3) = (x:real^3)` ASSUME_TAC THENL
                                [POP_ASSUM MP_TAC THEN VECTOR_ARITH_TAC;
                                 SET_TAC[]]];
                     SUBGOAL_THEN `(norm ((w:real^3) - (x:real^3)) * inv (norm (w - x)))= &1` ASSUME_TAC THENL
		                               [POP_ASSUM MP_TAC THEN MP_TAC(ISPEC `norm ((w:real^3)-(x:real^3))` REAL_MUL_RINV) THEN MESON_TAC[];
                          ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_ARITH `&1 % (v:real^3)= v`] THEN VECTOR_ARITH_TAC]]]]]]];
MESON_TAC[]]

);;



let proj_fan_is_continuous=prove(`!x:real^3. (proj_fan x:real^3->real^3) continuous_on (UNIV DELETE x)`,
GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON  THEN  REWRITE_TAC[IN_DELETE; IN_UNIV] THEN REWRITE_TAC [proj_fan] 
THEN  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_MUL  THEN 
SUBGOAL_THEN `(\y:real^3. y) continuous at (x':real^3)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[CONTINUOUS_AT_ID];
   SUBGOAL_THEN `(\y:real^3. (x:real^3)) continuous at (x':real^3)` ASSUME_TAC THENL
    [ASM_SIMP_TAC[CONTINUOUS_CONST];
     SUBGOAL_THEN `(\y:real^3. y-(x:real^3)) continuous at (x':real^3)` ASSUME_TAC THENL
        [ASM_SIMP_TAC[CONTINUOUS_SUB];
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM(ISPEC `lift` o_DEF); GSYM(ISPEC `inv` o_DEF)] THEN MATCH_MP_TAC CONTINUOUS_AT_INV THEN
        ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ;] THEN ASSUME_TAC(CONTINUOUS_AT_LIFT_NORM) THEN
        MP_TAC( ISPECL [ `(\y:real^3. y - (x:real^3))`; `(lift o norm ):real^3->real^1`; `x':real^3`] CONTINUOUS_AT_COMPOSE ) THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_DEF]]]]);;

 

(*------------------------------------------------------------------------*)
(*------------------------------------------------------------------------*)


let r_fan=new_definition`r_fan (a:real) (b:real) (c:real) = { y:real^3 | y$1 > &0  /\  y$2 > a  /\ y$2 < b /\ y$3 > &0 /\ y$3 < c}`;;


let r1_le_fan=new_definition`r1_le_fan (a:real)={ y:real^3 | y$1 > a}`;; 

let r2_le_fan=new_definition`r2_le_fan (a:real)={ y:real^3 |  y$2 > a}`;; 


let r3_le_fan=new_definition`r3_le_fan (a:real)={ y:real^3 | y$3 > a}`;; 


let r1_ge_fan=new_definition`r1_ge_fan (a:real)={ y:real^3 |  y$1 < a}`;;

let r2_ge_fan=new_definition`r2_ge_fan (a:real)={ y:real^3 |  y$2 < a}`;;

let r3_ge_fan=new_definition`r3_ge_fan (a:real)={ y:real^3 |  y$3 < a}`;;




let r_fan_is_inter_halfspace=prove(`!a:real b:real c:real. 
r_fan a b c = r1_le_fan (&0) INTER r2_le_fan a INTER r2_ge_fan b INTER r3_le_fan (&0) INTER r3_ge_fan c`,
REWRITE_TAC[r_fan; r1_le_fan; r2_le_fan; r2_ge_fan; r3_le_fan; r3_ge_fan; INTER; IN_ELIM_THM]);;

  

 

let r1_ge_is_convex_fan = prove(`!a:real. convex (r1_ge_fan a) `,REWRITE_TAC[r1_ge_fan] THEN REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT]);;

CONVEX_HALFSPACE_COMPONENT_LT;;

let r2_ge_is_convex_fan = prove(`!a:real. convex (r2_ge_fan a) `,
REWRITE_TAC[r2_ge_fan] THEN REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT]);;

let r3_ge_is_convex_fan = prove(`!a:real. convex (r3_ge_fan a) `,
REWRITE_TAC[r3_ge_fan] THEN REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT]);;

let r1_le_is_convex_fan = prove(`!a:real. convex (r1_le_fan a) `,
REWRITE_TAC[r1_le_fan] THEN REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GT]);;


let r2_le_is_convex_fan = prove(`!a:real. convex (r2_le_fan a) `,
REWRITE_TAC[r2_le_fan] THEN REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GT]);;


let r3_le_is_convex_fan = prove(`!a:real. convex (r3_le_fan a) `,
REWRITE_TAC[r3_le_fan] THEN REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GT]);;


let r_is_connected_fan=prove(`!a:real b:real c:real. connected (r_fan a b c)`,
   (let lemma = prove(`!a:real b:real c:real. convex (r_fan a b c)`,
ASSUME_TAC (r_fan_is_inter_halfspace) THEN ASM_REWRITE_TAC[] THEN
ASSUME_TAC (r1_ge_is_convex_fan) THEN ASSUME_TAC ( r2_ge_is_convex_fan) THEN
ASSUME_TAC (r3_ge_is_convex_fan) THEN ASSUME_TAC(r1_le_is_convex_fan) THEN
ASSUME_TAC(r2_le_is_convex_fan) THEN ASSUME_TAC( r3_le_is_convex_fan) THEN
ASM_MESON_TAC[CONVEX_INTER]) 
 in
SUBGOAL_THEN `!a:real b:real c:real. convex (r_fan a b c)` ASSUME_TAC 
THENL [MESON_TAC[lemma];
       ASM_MESON_TAC[CONVEX_CONNECTED]]));;




(*------------------------------------------------------------*)
(* change spherical coordinate in fan                         *)
(*------------------------------------------------------------*)


let change_spherical_coordinate_fan= new_definition`change_spherical_coordinate_fan (x:real^3) (v:real^3) (u:real^3) = (\(y:real^3).  x + ((y$1) * (cos (y$2)) * (sin (y$3))) % (e1_fan x v u)+ ((y$1) * (sin (y$2)) *(sin (y$3))) % (e2_fan x v u)+ ((y$1) * (cos (y$3))) %(e3_fan x v u))` ;;






(*---------------------------------------------------------------------------------------*)
(* the function of change coordinate is(spherecial) continuous                     *)
(*---------------------------------------------------------------------------------------*)








let the_change_spherical_coordinate_is_continuous_fan=prove( `(\x:real^1. (lift o (cos o drop)) (x)) continuous_on (UNIV:real^1->bool) /\ (\x:real^1. (lift o (sin o drop))( x)) continuous_on (UNIV:real^1->bool)
==>
(!x:real^3 v:real^3 u:real^3. (change_spherical_coordinate_fan x v u) continuous_on  UNIV)`,

 (    let lemma=prove(`!f s r. f continuous_on s /\ (r SUBSET s)==> f continuous_on r`, REWRITE_TAC[continuous_on; SUBSET] THEN MESON_TAC[]) in


DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[change_spherical_coordinate_fan] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN 
STRIP_TAC THENL (*1*)[REWRITE_TAC[CONTINUOUS_ON_CONST];(*1*)
                 MATCH_MP_TAC CONTINUOUS_ON_ADD
		   THEN  STRIP_TAC THENL
		     (*2*) [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_MUL 
			THEN  REWRITE_TAC[o_DEF;CONTINUOUS_ON_CONST; LIFT_CMUL ] ) 
			 THEN STRIP_TAC THENL 
                           (*3*) [MATCH_MP_TAC (ISPECL [`1`; `(UNIV:real^3->bool)`] CONTINUOUS_ON_LIFT_COMPONENT) 
			       THEN REWRITE_TAC[DIMINDEX_3] THEN REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 3`];
(*3*)
			     MATCH_MP_TAC CONTINUOUS_ON_MUL 
			       THEN REWRITE_TAC[o_DEF;CONTINUOUS_ON_CONST; LIFT_CMUL ] 
			       THEN STRIP_TAC THENL
                                  (*4*) [MP_TAC(ISPECL [ `(lift o (\x:real^3. x$2))`; `(lift o (cos o drop))`; `(UNIV:real^3->bool)` ] CONTINUOUS_ON_COMPOSE) THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC
				    THEN STRIP_TAC THENL
                                       (*5*)[MATCH_MP_TAC (ISPECL [`2`; `(UNIV:real^3->bool)`] CONTINUOUS_ON_LIFT_COMPONENT) 
			       THEN REWRITE_TAC[DIMINDEX_3] THEN REWRITE_TAC[ARITH_RULE `1 <= 2 /\ 2 <= 3`];(*5*)
					SUBGOAL_THEN ` (IMAGE (\x:real^3. lift (x$2)) (UNIV:real^3->bool)) SUBSET (UNIV:real^1->bool)` ASSUME_TAC

					  THENL (*6*)[SET_TAC[];(*6*)
						      MP_TAC(ISPECL[`(\x:real^1. lift(cos (drop x)))`; `UNIV:real^1->bool`; ` (IMAGE (\x:real^3. lift (x$2)) (UNIV:real^3->bool))`]lemma) THEN DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC  THEN REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[o_DEF] THEN MESON_TAC[]](*6*)](*5*);(*4*)

					 MP_TAC(ISPECL [ `(lift o (\x:real^3. x$3))`; `(lift o (sin o drop))`; `(UNIV:real^3->bool)` ] CONTINUOUS_ON_COMPOSE) THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC
				    THEN STRIP_TAC THENL
                                       (*5*)[MATCH_MP_TAC (ISPECL [`3`; `(UNIV:real^3->bool)`] CONTINUOUS_ON_LIFT_COMPONENT) 
			       THEN REWRITE_TAC[DIMINDEX_3] THEN REWRITE_TAC[ARITH_RULE `1 <= 3 /\ 3 <= 3`];
(*5*)
					SUBGOAL_THEN ` (IMAGE (\x:real^3. lift (x$3)) (UNIV:real^3->bool)) SUBSET (UNIV:real^1->bool)` ASSUME_TAC

					  THENL (*6*)[SET_TAC[];(*6*)
						      MP_TAC(ISPECL[`(\x:real^1. lift(sin (drop x)))`; `UNIV:real^1->bool`; ` (IMAGE (\x:real^3. lift (x$3)) (UNIV:real^3->bool))`]lemma) THEN DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC  THEN REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[o_DEF] THEN MESON_TAC[]](*6*)](*5*)](*4*)](*3*);(*2*)
			
			    MATCH_MP_TAC CONTINUOUS_ON_ADD
		   THEN  STRIP_TAC THENL
		     (*21*) [REPEAT(MATCH_MP_TAC CONTINUOUS_ON_MUL 
			THEN  REWRITE_TAC[o_DEF;CONTINUOUS_ON_CONST; LIFT_CMUL ] ) 
			 THEN STRIP_TAC THENL
                           (*3*) [MATCH_MP_TAC (ISPECL [`1`; `(UNIV:real^3->bool)`] CONTINUOUS_ON_LIFT_COMPONENT) 
			       THEN REWRITE_TAC[DIMINDEX_3] THEN REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 3`];
(*3*)
			     MATCH_MP_TAC CONTINUOUS_ON_MUL 
			       THEN REWRITE_TAC[o_DEF;CONTINUOUS_ON_CONST; LIFT_CMUL ] 
			       THEN STRIP_TAC THENL
                                  (*4*) [MP_TAC(ISPECL [ `(lift o (\x:real^3. x$2))`; `(lift o (sin o drop))`; `(UNIV:real^3->bool)` ] CONTINUOUS_ON_COMPOSE) THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC
				    THEN STRIP_TAC THENL
                                       (*5*)[MATCH_MP_TAC (ISPECL [`2`; `(UNIV:real^3->bool)`] CONTINUOUS_ON_LIFT_COMPONENT) 
			       THEN REWRITE_TAC[DIMINDEX_3] THEN REWRITE_TAC[ARITH_RULE `1 <= 2 /\ 2 <= 3`];(*5*)
					SUBGOAL_THEN ` (IMAGE (\x:real^3. lift (x$2)) (UNIV:real^3->bool)) SUBSET (UNIV:real^1->bool)` ASSUME_TAC

					  THENL (*6*)[SET_TAC[];(*6*)
						      MP_TAC(ISPECL[`(\x:real^1. lift(sin (drop x)))`; `UNIV:real^1->bool`; ` (IMAGE (\x:real^3. lift (x$2)) (UNIV:real^3->bool))`]lemma) THEN DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC  THEN REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[o_DEF] THEN MESON_TAC[]](*6*)](*5*);(*4*)

					 MP_TAC(ISPECL [ `(lift o (\x:real^3. x$3))`; `(lift o (sin o drop))`; `(UNIV:real^3->bool)` ] CONTINUOUS_ON_COMPOSE) THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC
				    THEN STRIP_TAC THENL
                                       (*5*)[MATCH_MP_TAC (ISPECL [`3`; `(UNIV:real^3->bool)`] CONTINUOUS_ON_LIFT_COMPONENT) 
			       THEN REWRITE_TAC[DIMINDEX_3] THEN REWRITE_TAC[ARITH_RULE `1 <= 3 /\ 3 <= 3`];
(*5*)
					SUBGOAL_THEN ` (IMAGE (\x:real^3. lift (x$3)) (UNIV:real^3->bool)) SUBSET (UNIV:real^1->bool)` ASSUME_TAC

					  THENL (*6*)[SET_TAC[];(*6*)
						      MP_TAC(ISPECL[`(\x:real^1. lift(sin (drop x)))`; `UNIV:real^1->bool`; ` (IMAGE (\x:real^3. lift (x$3)) (UNIV:real^3->bool))`]lemma) THEN DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC  THEN REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[o_DEF] THEN MESON_TAC[]](*6*)](*5*)](*4*)](*3*);(*2*)
					
REPEAT (MATCH_MP_TAC CONTINUOUS_ON_MUL 
			THEN  REWRITE_TAC[o_DEF;CONTINUOUS_ON_CONST; LIFT_CMUL ])
			 THEN STRIP_TAC THENL
                           (*3*) [MATCH_MP_TAC (ISPECL [`1`; `(UNIV:real^3->bool)`] CONTINUOUS_ON_LIFT_COMPONENT) 
			       THEN REWRITE_TAC[DIMINDEX_3] THEN REWRITE_TAC[ARITH_RULE `1 <= 1 /\ 1 <= 3`];
(*3*)
			          MP_TAC(ISPECL [ `(lift o (\x:real^3. x$3))`; `(lift o (cos o drop))`; `(UNIV:real^3->bool)` ] CONTINUOUS_ON_COMPOSE) THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC
				    THEN STRIP_TAC THENL
                                       (*5*)[MATCH_MP_TAC (ISPECL [`3`; `(UNIV:real^3->bool)`] CONTINUOUS_ON_LIFT_COMPONENT) 
			       THEN REWRITE_TAC[DIMINDEX_3] THEN REWRITE_TAC[ARITH_RULE `1 <= 3 /\ 3 <= 3`];(*5*)
					SUBGOAL_THEN ` (IMAGE (\x:real^3. lift (x$3)) (UNIV:real^3->bool)) SUBSET (UNIV:real^1->bool)` ASSUME_TAC

					  THENL (*6*)[SET_TAC[];(*6*)
						      MP_TAC(ISPECL[`(\x:real^1. lift(cos (drop x)))`; `UNIV:real^1->bool`; ` (IMAGE (\x:real^3. lift (x$3)) (UNIV:real^3->bool))`]lemma) THEN DISCH_TAC THEN POP_ASSUM MATCH_MP_TAC  THEN REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[o_DEF] THEN MESON_TAC[]](*6*)](*5*)]]]]));;(*3*)
*)