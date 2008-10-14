

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



 let power_map= new_recursive_definition num_RECURSION `(power_map f 0 = i_fan)/\(power_map f  (SUC n)= o_fun f  (power_map f  n))`;;



 let power_map_point= new_recursive_definition num_RECURSION `(power_map_point f v w 0 = w)/\(power_map_point f v w  (SUC n)= f v (power_map_point f v w n))`;;


 let power_n_fan= new_definition`power_n_fan n=(\(x,v,w,w1). (x,v,(power_map_point sigma_fan v w n),(power_map_point sigma_fan v w (SUC n))))`;; 


 let a_node_fan=new_definition`a_node_fan (x,v,w,w1)={a | ?n. a=(power_map  n_fan n) (x,v,w,sigma_fan v w)}`;;






 let X= new_definition`X fan(x,V,E)={v | ?e. (E e)/\(v IN aff_ge {x} e)}`;;

 let Y= new_definition`Y fan(x,V,E)={v:real^3 | ?e. (E e)/\(~(v IN aff_ge {x} e))}`;;

 let w_dart=new_definition`w_dart x v w w1= wedge x v w (sigma_fan v w)`;;

 let azim_fan=new_definition`azim_fan x v w w1= azim x v w w1`;;

 let w_dart0=new_definition`w_dart0 x v w w1 y=(w_dart x v w w1) INTER (rcone_gt x v y)`;;

 let c_fan=new_definition`c_fan x v w y ={c | (c IN aff_ge {x} {v,w})/\ (~((c IN rcone_gt x v y)\/(c IN rcone_gt x w y)))}`;;




*************************************************
(* Proof remark 4.1 *)
let asfan=prove(`{w,v}={v,w}`, SET_TAC[]);;


let remark_fan1=prove(`!v w E. (w IN set_of_edges v E)<=>(v IN set_of_edges w E)`, 
REPEAT GEN_TAC THEN REWRITE_TAC[set_of_edges] THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[asfan]);;




(* Proof Lemma 4.1 *)



let node_fan=prove(`!n. power_map n_fan n=power_n_fan n`, REWRITE_TAC[power_map; n_fan; power_n_fan; power_map_point] THEN INDUCT_TAC THEN REWRITE_TAC[power_map; power_map_point; i_fan;] THEN REWRITE_TAC[power_map_point; power_map] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[o_fun; p1; p2; p3; p4]);;


let lem_fan411=prove(`(!v w. sigma_fan v (inverse_sigma_fan v w)=w)==> (o_fun e_fan (o_fun n_fan f_fan)=i_fan)`, 
REWRITE_TAC[o_fun; e_fan; f_fan; n_fan; i_fan;] THEN REWRITE_TAC[p1; p2; p3; p4] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]);;

let lem_fan412=prove(`o_fun e_fan  e_fan =i_fan`, 
REWRITE_TAC[o_fun; e_fan; i_fan;] THEN REWRITE_TAC[p1; p2; p3; p4]);;

let e_fan_no_fix_point=prove(`!x v w w1. (v=w) <=>(e_fan(x,v,w,(sigma_fan v w))=(x,v,w,(sigma_fan v w)))`, 
REPEAT GEN_TAC THEN REWRITE_TAC[e_fan] THEN MESON_TAC[PAIR_EQ] );;

let f_fan_no_fix_point=prove(`!x v w w1. (f_fan(x,v,w,(sigma_fan v w))=(x,v,w,(sigma_fan v w)))==>(v=w)`, 
REPEAT GEN_TAC THEN REWRITE_TAC[f_fan] THEN MESON_TAC[PAIR_EQ] );;

let lem_fan4131=prove(`w = power_map_point sigma_fan v w m ==> (x,v,power_map_point sigma_fan v w m,
 sigma_fan v (power_map_point sigma_fan v w m) =
 x,v,w,sigma_fan v w)`, MESON_TAC[]);;

let lem_fan413=prove(`!x v w w1 n m. o_fun (power_map n_fan n)  e_fan (x,v,w,w1)=o_fun e_fan (power_map n_fan m) (x,v,w,w1)
==> (power_map n_fan m) (x,v,w,w1) =i_fan (x,v,w,w1)`, 
REWRITE_TAC[node_fan; o_fun; e_fan; power_n_fan; i_fan; p1; p2; p3; p4;] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN 
SUBGOAL_THEN `w=power_map_point sigma_fan v w m` ASSUME_TAC 
THENL [POP_ASSUM MP_TAC THEN MESON_TAC[PAIR_EQ]; 
POP_ASSUM MP_TAC THEN REWRITE_TAC[power_map_point] THEN MESON_TAC[lem_fan4131]]);;


let lem_fan414=prove(`!x v w w1 n. (power_map n_fan n) (x,v,w,w1)=e_fan (x,v,w,w1)==>(v=w)`, 
REWRITE_TAC[node_fan; e_fan; power_n_fan;]  THEN REPEAT GEN_TAC THEN MESON_TAC[PAIR_EQ]);;

(* Proof of Lemma 4.2 *)


let lemma421=prove(`a IN a_node_fan (x,v,w,w1)==>(?n. a=(x,v,(power_map_point sigma_fan v w n),(power_map_point sigma_fan v w (SUC n))))`, REWRITE_TAC[a_node_fan; IN_ELIM_THM; ] THEN REWRITE_TAC[node_fan] THEN REWRITE_TAC[power_n_fan]);;


