(* Hoang Le Truong *)

(* since you define C0,C1 independently, you need lemmas to relate this to other chapters.

lemmas 
`aff_gt {v} {v1,v2}={t1 % v+t2 % v1+t3 % v2 | ?t1 t2 t3. (t2 > &0)/\(t3 > &0)/\(t1+t2+t3= &1)}`;;

`aff_ge {v} {v1,v2}={t1 % v+t2 % v1+t3 % v2 | ?t1 t2 t3. (t2 >= &0)/\(t3 >= &0)/\(t1+t2+t3= &1)}`;;

*)

needs "Multivariate/vectors.ml";;    
needs "Examples/analysis.ml";;       
needs "Examples/transc.ml";;         
needs "definitions_kepler.ml";;




let graph = new_definition `graph E <=> (!e. E e ==> (e HAS_SIZE 2))`;;

let fan1 = new_definition`fan1(x,V,E):bool <=>  FINITE V /\ ~(V SUBSET {}) `;;

let fan2 = new_definition`fan2(x,V,E):bool <=>   ~(x IN V)`;;

let fan3=new_definition`fan3(x,V,E):bool <=> (!v. (v IN V) ==> cyclic_set {w | {v,w} IN E } x v)`;;

let fan4 = new_definition`fan4(x,V,E):bool<=>  (!e. (e IN E) ==> (aff_gt {x} e  INTER V={}))`;;

let fan5 = new_definition`fan5(x,V,E):bool<=> (!e f. (e IN E)/\ (f IN E) /\ ~(e=f) ==> (aff_gt {x} e INTER aff_gt {x} f ={}))`;;

let fan = new_definition`fan(x,V,E)<=>  ((UNIONS E) SUBSET V) /\ graph(E)/\ fan1(x,V,E)/\ fan2(x,V,E)/\ fan3(x,V,E)/\ fan4 (x,V,E) /\ fan5(x,V,E)`;;

let base_point_fan=new_definition`base_point_fan (x,V,E)=x`;;

let set_of_edges=new_definition`set_of_edges v E={w|{v,w} IN E}`;;

let asfan=prove(`{w,v}={v,w}`, SET_TAC[]);;

let remark_fan1=prove(`!v w E. (w IN set_of_edges v E)<=>(v IN set_of_edges w E)`, REPEAT GEN_TAC THEN REWRITE_TAC[set_of_edges] THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[asfan]);;



let azim_cycle_fan= new_definition`azim_cycle_fan   = 
(?sigma. !v w proj e1 e2 e3 x V E. 
(fan(x, V, E))/\(V v)/\({v,w} IN E)/\((dist(v,w)) % e3 = (x-v))/\
(orthonormal e1 e2 e3) /\
(!u a b. (proj u = (a,b)) <=> (?h. (u = v + a % e1 + b % e2 + h % e3))) 
==> (proj (sigma  v w) = polar_cycle (IMAGE proj {y|{v,y} IN E}) (proj w))) `;;



 let azim_cycle_fan1= prove (`?sigma. !v w proj e1 e2 e3 x V E. 
(azim_cycle_fan) ==> ((fan(x, V, E))/\(V v)/\({v,w} IN E)/\((dist(v,w)) % e3 = (x-v))/\
(orthonormal e1 e2 e3) /\
(!u a b. (proj u = (a,b)) <=> (?h. (u = v + a % e1 + b % e2 + h % e3))) 
==> (proj (sigma  v w) = polar_cycle (IMAGE proj {y|{v,y} IN E}) (proj w)))`,
	(REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM;GSYM RIGHT_IMP_FORALL_THM]) THEN
	  (REWRITE_TAC[azim_cycle_fan])
	   );;

let sigma_fan= new_specification ["sigma_fan"] azim_cycle_fan1;;


let D1=new_definition`D1 fan(x,V,E)={(x,v,w,w1)|(V v)/\(w IN set_of_edges v E)/\(w1=sigma_fan v w)}`;;


let D2=new_definition`D2 fan(x,V,E)={ (x,v)|(V v)/\(set_of_edges v E={})}`;;

(* This last part generates an error. -t.hales
   For example, MATH_MP_TAC is not defined. *)

(*

let D_fan=new_definition`D_fan fan(x,V,E)= D1 fan(x,V,E) UNION D2 fan(x,V,E)`;;

*)

let inverse_sigma_fan=new_definition`inverse_sigma_fan v w = @a. sigma_fan v a=w`;;

let e_fan=new_definition`e_fan=(\(x,v,w,w1). (x,w,v,(sigma_fan w v)))`;;

let f_fan=new_definition`f_fan = (\(x,v,w,w1). (x,w,(inverse_sigma_fan w v),v) )`;;

let n_fan=new_definition`n_fan=(\(x,v,w,w1). (x,v,(sigma_fan v w),(sigma_fan v (sigma_fan v w))))`;;

let i_fan=new_definition`i_fan=(\(x,v,w,w1). (x,v,w,(sigma_fan v w)))`;;

let p1=new_definition`p1=(\(x,v,w,w1). x)`;;

let p2=new_definition`p2=(\(x,v,w,w1). v)`;;

let p3=new_definition`p3=(\(x,v,w,w1). w)`;;

let p4=new_definition`p4=(\(x,v,w,w1). w1)`;;

let o_fun=new_definition`!(f:A#B#C#D->A#B#C#D) (g:A#B#C#D->A#B#C#D). o_fun f g =(\(x:A,y:B,z:C,t:D).  f (p1 (g (x,y,z,t)),p2(g(x,y,z,t)),p3(g(x,y,z,t)),p4(g(x,y,z,t))))`;;

let lem_fan1=prove(`(!v w. sigma_fan v (inverse_sigma_fan v w)=w)==> (o_fun e_fan (o_fun n_fan f_fan)=i_fan)`, 
REWRITE_TAC[o_fun; e_fan; f_fan; n_fan; i_fan;] THEN REWRITE_TAC[p1; p2; p3; p4] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let lem_fan2=prove(`o_fun e_fan  e_fan =i_fan`, 
REWRITE_TAC[o_fun; e_fan; i_fan;] THEN REWRITE_TAC[p1; p2; p3; p4]);;

let e_fan_no_fix_point=prove(`!x v w w1. (v=w) <=>(e_fan(x,v,w,(sigma_fan v w))=(x,v,w,(sigma_fan v w)))`, 
REPEAT GEN_TAC THEN REWRITE_TAC[e_fan] THEN MESON_TAC[PAIR_EQ] );;

let f_fan_no_fix_point=prove(`!x v w w1. (v=w) <=>(f_fan(x,v,w,(sigma_fan v w))=(x,v,w,(sigma_fan v w)))`, 
REPEAT GEN_TAC THEN REWRITE_TAC[f_fan] THEN MESON_TAC[PAIR_EQ] );;
