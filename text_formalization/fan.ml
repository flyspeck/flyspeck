(* Hoang Le Truong *)

(* since you define C0,C1 independently, you need lemmas to relate this to other chapters.

lemmas 
`aff_gt {v} {v1,v2}={t1 % v+t2 % v1+t3 % v2 | ?t1 t2 t3. (t2 > &0)/\(t3 > &0)/\(t1+t2+t3= &1)}`;;

`aff_ge {v} {v1,v2}={t1 % v+t2 % v1+t3 % v2 | ?t1 t2 t3. (t2 >= &0)/\(t3 >= &0)/\(t1+t2+t3= &1)}`;;

*)

needs "Multivariate/flyspeck.ml";;
needs "sphere.hl";;

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
(  !x:real^3 V E. ?sigma. !proj e1 e2 e3 v w. 
(fan(x, V, E) /\ (V v) /\ ({v,w} IN E) /\ ((dist(v,w)) % e3 = (x-v)) /\
(orthonormal e1 e2 e3) /\
(!u a b. (proj u = (a,b)) <=> (?h. (u = v + a % e1 + b % e2 + h % e3)))) 
==> (  (proj (sigma  v w) = polar_cycle (IMAGE proj {y|{v,y} IN E}) (proj w)))) `;;

let azim_cycle_fan1 = REWRITE_RULE[SKOLEM_THM] azim_cycle_fan;;

let azim_cycle_fan2=prove(`?sigma. !x:real^3 V E proj e1 e2 e3 v w. 
(azim_cycle_fan)==>
(fan(x, V, E) /\ (V v) /\ ({v,w} IN E) /\ ((dist(v,w)) % e3 = (x-v)) /\
(orthonormal e1 e2 e3) /\
(!u a b. (proj u = (a,b)) <=> (?h. (u = v + a % e1 + b % e2 + h % e3)))) 
==> (  (proj (sigma x V E v w) = polar_cycle (IMAGE proj {y|{v,y} IN E}) (proj w))) `,
REWRITE_TAC[GSYM RIGHT_IMP_FORALL_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN 
REWRITE_TAC[azim_cycle_fan1]);;
	

 
let sigma_fan= new_specification ["sigma_fan"] azim_cycle_fan2;;



let D1=new_definition`D1 (x,V,E) ={(x:real^3,v:real^3,w:real^3,w1:real^3)|(V v)/\(w IN set_of_edges v E)/\(w1 = sigma_fan x V E v w)}`;;



let D2=new_definition`D2 (x,V,E)={ (x,v)|(V v)/\(set_of_edges v E={})}`;;


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

let w_dart=new_definition`w_dart x V E x v w w1= wedge x v w (sigma_fan x V E v w)`;;

let azim_fan=new_definition`azim_fan x v w w1= azim x v w w1`;;
(*
let w_dart0=new_definition`w_dart0 x v w w1 y=(w_dart x V E x v w w1) INTER (rcone_gt x v y)`;;

let c_fan=new_definition`c_fan x v w y ={c | (c IN aff_ge {x} {v,w})/\ (~((c IN rcone_gt x v y)\/(c IN rcone_gt x w y)))}`;; 
*)




(* ************************************************* *)
(* Proof remark rem:fan *)
let asfan=prove(`{w,v}={v,w}`, SET_TAC[]);;


let remark_fan1=prove(`!v w E. (w IN set_of_edges v E)<=>(v IN set_of_edges w E)`, 
REPEAT GEN_TAC THEN REWRITE_TAC[set_of_edges] THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[asfan]);;




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

(* Proof of Lemma [VBTIKLP] *)


let lemma62=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 w:real^3 w1:real^3. a IN a_node_fan x V E (x,v,w,w1)==>(?n. a=(x,v,(power_map_points sigma_fan x V E v w n),(power_map_points sigma_fan x V E v w (SUC n))))`, REWRITE_TAC[a_node_fan; IN_ELIM_THM; ] THEN REWRITE_TAC[node_fan] THEN REWRITE_TAC[power_n_fan]);;


let complement_set= new_definition`complement_set {x:real^3, v:real^3} = {y:real^3| ~(y IN aff {x,v})} `;;

let subset_aff=prove(`!x:real^3 v:real^3. (aff{x, v} SUBSET (UNIV:real^3->bool))`, REPEAT GEN_TAC THEN SET_TAC[]);;


let union_aff=prove(`!x v:real^3. (UNIV:real^3->bool) = aff{x, v} UNION  complement_set {x, v}  `,
REPEAT GEN_TAC  THEN REWRITE_TAC[complement_set] THEN SET_TAC[]);;


let f_azim_fan= new_definition` f_azim_fan x V E v u=
(\i. azim_fan x v u (power_map_points sigma_fan x V E v u i))`;;


let lemma_disjiont_exists_fan1=prove(` !x:real^3 v:real^3 u:real^3 y:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) n:num. 
(y IN complement_set {x,v})/\(f_azim_fan x V E v u (0) <= azim_fan x v u y)/\
(f_azim_fan x V E v u (0) = azim_fan x v u y)/\
(f_azim_fan x V E v u (n) > azim_fan x v u y)/\(CARD E=n)
/\(!i:num. (i IN (0..(n-1)))/\(f_azim_fan x V E v u (i)<f_azim_fan x V E v u (i+1)))
==>(?i. (i IN (0..(n-1)))/\
((f_azim_fan x V E v u (i) = azim_fan x v u y)
\/
((f_azim_fan x V E v u (i) < azim_fan x v u y)
/\(azim_fan x v u y < f_azim_fan x V E v u(i+1)))))`, MESON_TAC[]);;





let lemma_disjiont_exists_fan2=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 n:num. 
azim x v u u = &0 ==> f_azim_fan x V E v u (0) = &0`, 
REWRITE_TAC[f_azim_fan] THEN REWRITE_TAC[power_map_points] THEN REWRITE_TAC[azim_fan]);;


let lemma_disjiont_exists_fan3=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 n:num. 
(azim x v u u = &0)/\ (&0<= azim_fan x v u y) ==> (f_azim_fan x V E v u (0) <= azim_fan x v u y)`, 
MESON_TAC[lemma_disjiont_exists_fan2]);;



let wedge_fan2=new_definition`wedge_fan2 (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) =
{y:real^3 | ( f_azim_fan x V E v u (i) = azim_fan x v u y)/\( y IN complement_set {x, v})}`;;

(*wedge_fan2=aff_gt*)

let COMPLEMENT_SET_FAN=prove(`!x:real^3 v:real^3 u:real^3 y:real^3 w:real^3 t1:real t2:real t3:real. 
(!x:real^3 v:real^3. aff {x , v} = {y:real^3| ?t1:real t2:real. (t1 + t2 = &1 )/\ (y = t1 % x + t2 % v )}) /\
~( w IN aff {x, v}) /\ ~(t3 = &0) /\ (t1 + t2 + t3 = &1)
==> t1 % x + t2 % v + t3 % w IN
 complement_set {x, v}`,
 REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[complement_set; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN 
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


let aff_imp_wedge_fan2a=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 i:num. 
(!x:real^3 v:real^3. aff {x , v} = {y:real^3| ?t1:real t2:real. (t1 + t2 = &1 )/\ (y = t1 % x + t2 % v )}) /\
~( (power_map_points sigma_fan x V E v u i) IN aff {x, v})
/\ (!x:real^3 v:real^3 u:real^3 w:real^3 t1:real t2:real t3:real. ~(t3 = &0) /\ (t1 + t2 + t3 = &1)  ==> azim x v u w =
 azim x v u (t1 % x + t2 % v + t3 % w))
==> 

!y:real^3.  {y:real^3 
| ?t1:real t2:real t3:real. (t3 > &0)/\(t1+t2+t3= &1)/\( y = t1 % x + t2 % v + t3 % (power_map_points sigma_fan x V E v u i))} y
==> wedge_fan2 x V E v u i y`,
REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN REWRITE_TAC[wedge_fan2; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN 
REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `~((t3:real) = &0)` ASSUME_TAC THENL
   [REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `t1 % x + t2 % v + t3 % power_map_points sigma_fan x V E v u i IN
 complement_set {x, v}` ASSUME_TAC THENL
      [ASM_MESON_TAC[COMPLEMENT_SET_FAN];
       ASM_REWRITE_TAC[] THEN REWRITE_TAC[f_azim_fan; azim_fan] THEN ASM_MESON_TAC[]]]);;


let aff_imp_wedge_fan2=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 i:num. 
(!x:real^3 v:real^3. aff {x , v} = {y:real^3| ?t1:real t2:real. (t1 + t2 = &1 )/\ (y = t1 % x + t2 % v )}) /\
~( (power_map_points sigma_fan x V E v u i) IN aff {x, v})
/\ (!x:real^3 v:real^3 u:real^3 w:real^3 t1:real t2:real t3:real. ~(t3 = &0) /\ (t1 + t2 + t3 = &1)  ==> azim x v u w =
 azim x v u (t1 % x + t2 % v + t3 % w))
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. aff_gt {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 > &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
==> 

!y:real^3.  aff_gt {x , v} {power_map_points sigma_fan x V E v u i} y
==> (wedge_fan2 x V E v u i) y`,
REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN REWRITE_TAC[wedge_fan2; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN 
REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `~((t3:real) = &0)` ASSUME_TAC THENL
   [REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `t1 % x + t2 % v + t3 % power_map_points sigma_fan x V E v u i IN
 complement_set {x, v}` ASSUME_TAC THENL
      [ASM_MESON_TAC[COMPLEMENT_SET_FAN];
       ASM_REWRITE_TAC[] THEN REWRITE_TAC[f_azim_fan; azim_fan] THEN ASM_MESON_TAC[]]]);;

let aff_gt_subset_wedge_fan2=prove(`!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 i:num. 
(!x:real^3 v:real^3. aff {x , v} = {y:real^3| ?t1:real t2:real. (t1 + t2 = &1 )/\ (y = t1 % x + t2 % v )}) /\
~( (power_map_points sigma_fan x V E v u i) IN aff {x, v})
/\ (!x:real^3 v:real^3 u:real^3 w:real^3 t1:real t2:real t3:real. ~(t3 = &0) /\ (t1 + t2 + t3 = &1)  ==> azim x v u w =
 azim x v u (t1 % x + t2 % v + t3 % w))
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. aff_gt {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 > &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
==> 

 aff_gt {x , v} {power_map_points sigma_fan x V E v u i}  SUBSET wedge_fan2 x V E v u i `,
REWRITE_TAC[SUBSET] THEN
REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN REWRITE_TAC[wedge_fan2; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN 
REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `~((t3:real) = &0)` ASSUME_TAC THENL
   [REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
    SUBGOAL_THEN `t1 % x + t2 % v + t3 % power_map_points sigma_fan x V E v u i IN
 complement_set {x, v}` ASSUME_TAC THENL
      [ASM_MESON_TAC[COMPLEMENT_SET_FAN];
       ASM_REWRITE_TAC[] THEN REWRITE_TAC[f_azim_fan; azim_fan] THEN ASM_MESON_TAC[]]]);;


let wedge_fan2_subset_aff_gt=prove(`(!x:real^3 v:real^3. aff {x , v} = {y:real^3| ?t1:real t2:real. (t1 + t2 = &1 )/\ (y = t1 % x + t2 % v )}) /\
~( (power_map_points sigma_fan x V E v u i) IN aff {x, v})
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. aff_gt {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 > &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. {y:real^3 |  azim x v u w =
 azim x v u y}=aff_gt {x , v} {w})
==> 
(!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 i:num. 
 wedge_fan2 x V E v u i SUBSET aff_gt {x , v} {power_map_points sigma_fan x V E v u i} )   `,

STRIP_TAC THEN REPEAT GEN_TAC  THEN REWRITE_TAC[SUBSET] THEN GEN_TAC THEN REWRITE_TAC[wedge_fan2;IN_ELIM_THM] THEN
POP_ASSUM MP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN
POP_ASSUM (MP_TAC o SPECL [`x':real^3`;`v':real^3`;`u':real^3`;`(power_map_points sigma_fan x'  (V':real^3->bool) (E':(real^3->bool)->bool) v' u' (i':num)):real^3`; `x'':real^3`]) THEN
REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[f_azim_fan; azim_fan] THEN SET_TAC[]);;



let wedge_fan2_equal_aff_gt=prove(` 
(!x:real^3 v:real^3. aff {x , v} = {y:real^3| ?t1:real t2:real. (t1 + t2 = &1 )/\ (y = t1 % x + t2 % v )})
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. aff_gt {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 > &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
/\ (!x:real^3 v:real^3 u:real^3 w:real^3 t1:real t2:real t3:real. ~(t3 = &0) /\ (t1 + t2 + t3 = &1)  ==> azim x v u w =
 azim x v u (t1 % x + t2 % v + t3 % w))
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. {y:real^3 |  azim x v u w =
 azim x v u y}=aff_gt {x , v} {w})
==> 
(!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 i:num.
~( (power_map_points sigma_fan x V E v u i) IN aff {x, v})
==>
 wedge_fan2 x V E v u i = aff_gt {x , v} {power_map_points sigma_fan x V E v u i})    `,
  
STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
SUBGOAL_THEN `wedge_fan2 x V E v u i SUBSET aff_gt {x , v} {power_map_points sigma_fan x V E v u i}` ASSUME_TAC
THENL
  [ASM_MESON_TAC[ wedge_fan2_subset_aff_gt];
   SUBGOAL_THEN `
      aff_gt {(x:real^3), (v:real^3)} {power_map_points sigma_fan x V E v u i}  SUBSET wedge_fan2 (x:real^3) V E (v:real^3) (u:real^3) (i:num)` ASSUME_TAC  THENL
       [REWRITE_TAC[SUBSET] THEN GEN_TAC THEN ASM_REWRITE_TAC[] 
        THEN REWRITE_TAC[wedge_fan2; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN 
        REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN 
        SUBGOAL_THEN `~((t3:real) = &0)` ASSUME_TAC  THENL
            [REPEAT (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;                
             SUBGOAL_THEN `t1 % x + t2 % v + t3 % power_map_points sigma_fan x V E v u i IN 
                complement_set {x, v}` ASSUME_TAC THENL
                      [ASM_MESON_TAC[COMPLEMENT_SET_FAN];
                       ASM_REWRITE_TAC[] THEN REWRITE_TAC[f_azim_fan; azim_fan] THEN ASM_MESON_TAC[]]];

         SET_TAC[]]]);;


(************)

let wedge_fan3=new_definition`wedge_fan3 (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) =
{y:real^3 | ( f_azim_fan x V E v u (i) < azim_fan x v u y)/\
(azim_fan x v u y < f_azim_fan x V E v u (i+1))/\( y IN complement_set {x, v})}`;;

let wedge_fan6=new_definition`wedge_fan6 (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) ={y:real^3 | (( f_azim_fan x V E v u (i) = azim_fan x v u y)\/(( f_azim_fan x V E v u (i) < azim_fan x v u y)/\(azim_fan x v u y < f_azim_fan x V E v u (i+1))))/\( y IN complement_set {x, v})}`;;


let lemma_disjiont_union=prove(`!(x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num). wedge_fan6 x V E v u i=wedge_fan2 x V E v u i UNION wedge_fan3 x V E v u i`, REWRITE_TAC[wedge_fan2;wedge_fan3;wedge_fan6;FUN_EQ_THM; UNION] THEN GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM]
THEN MESON_TAC[]);;



let wedge_fans= new_recursive_definition num_RECURSION `(wedge_fans (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)  0 = wedge_fan6 x V E v u (0))/\(wedge_fans x V E v u (SUC n)=(wedge_fans x V E v u n) UNION wedge_fan6 x V E v u (SUC n))`;;

let complement_sets=new_definition`complement_sets (x:real^3)  (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3)  (n:num)=
{ y|(y IN complement_set {x,v})/\
(f_azim_fan x V E v u (0) < azim_fan x v u y)/\
(f_azim_fan x V E v u (0) = azim_fan x v u y)/\
(f_azim_fan x V E v u (n) > azim_fan x v u y)/\
(!i. (i IN (0..(n-1)))/\(f_azim_fan x V E v u (i) < f_azim_fan x V E v u (i+1))) } `;;



let lemma_disjiont_union1=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3  n:num. 
(y IN complement_sets x V E v u n) ==>(?i. (i IN (0..(n-1)))/\( y IN (wedge_fan6 x V E v u i)))`, REPEAT GEN_TAC THEN
REWRITE_TAC[complement_sets; wedge_fan6] THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;


let lemma_disjiont_union2=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 n. 
(?i. (i IN (0..(n-1)))/\ (y IN (wedge_fan6 x V E v u i))) ==> (y IN complement_set {x,v}) `, REPEAT GEN_TAC THEN REWRITE_TAC[complement_set; wedge_fan6] THEN
REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;






let lemma_disjiont_unions=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 n:num.(y IN UNIONS {wedge_fan6 x V E v u i| i IN (0..(n-1))}) <=> 
(?i. (i IN (0..(n-1)))/\ (y IN (wedge_fan6 x V E v u i)))  `,
REWRITE_TAC[UNIONS] THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;



let lemma_disjiont_unions2=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 n:num. 
(y IN UNIONS {wedge_fan6 x V E v u i | i IN (0..(n-1))}) ==>(y IN complement_set {x,v}) `,
REPEAT GEN_TAC THEN STRIP_TAC THEN 
SUBGOAL_THEN `(?i. (i IN (0..(n-1)))/\ (y IN (wedge_fan6 x V E v u i)))` ASSUME_TAC 
THENL
  [POP_ASSUM MP_TAC THEN MESON_TAC[lemma_disjiont_unions];
   POP_ASSUM MP_TAC THEN MESON_TAC[lemma_disjiont_union2]]);;






let lemma_disjiont_unions1= prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 y:real^3 n:num.
(y IN complement_sets x V E v u n) ==> (y IN UNIONS {wedge_fan6 x V E v u i | i IN (0..(n-1))})`,
REPEAT GEN_TAC THEN STRIP_TAC THEN 
SUBGOAL_THEN `(?i. (i IN (0..(n-1))) /\ (y IN (wedge_fan6 x V E v u i)))` ASSUME_TAC
THENL 
   [POP_ASSUM MP_TAC THEN MESON_TAC[lemma_disjiont_union1];
     POP_ASSUM MP_TAC THEN MESON_TAC[lemma_disjiont_unions]]);;








let disjiont_union1=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3  n:num.
complement_sets x V E v u n = complement_set {x,v}==>
(!y. ((y IN UNIONS {wedge_fan6 x V E v u i | i IN (0..(n-1))})<=>(y IN complement_set {x,v})))`,
REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN EQ_TAC 
THENL 
  [MESON_TAC[lemma_disjiont_unions2];
   SUBGOAL_THEN `(y IN complement_sets x V E v u n) ==> (y IN UNIONS {wedge_fan6 x V E v u i | i IN (0..(n-1))})` ASSUME_TAC
      THENL 
        [MESON_TAC[lemma_disjiont_unions1]; 
         REPEAT (POP_ASSUM MP_TAC) THEN MESON_TAC[]]]);;


let disjiont_union2=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 n:num.
complement_sets x V E v u n = complement_set {x,v}==>
(UNIONS {wedge_fan6 x V E v u i | i IN (0..(n-1))}= complement_set {x,v})`, 
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
SUBGOAL_THEN `(!y. ((y IN UNIONS {wedge_fan6 x V E v u i | i IN (0..(n-1))})<=>(y IN complement_set {x,v})))` ASSUME_TAC
THENL 
  [POP_ASSUM MP_TAC THEN MESON_TAC[disjiont_union1]; 
   POP_ASSUM MP_TAC THEN REWRITE_TAC[IN]]);;



let lemma_disjiont1=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 n:num.
(complement_sets x V E v u n = complement_set {x,v})==>
((UNIV:real^3->bool) = aff {x,v} UNION (UNIONS {wedge_fan6 x V E v u i | i IN (0..(n-1))}))`, 
REPEAT GEN_TAC THEN STRIP_TAC THEN
SUBGOAL_THEN `(UNIONS {wedge_fan6 x V E v u i | i IN (0..(n-1))} = complement_set {x,v})` ASSUME_TAC 
THENL 
 [POP_ASSUM MP_TAC THEN MESON_TAC[disjiont_union2];
 SUBGOAL_THEN `(UNIV:real^3->bool) = aff{x, v} UNION  complement_set {x, v}` ASSUME_TAC
     THENL
       [MESON_TAC[union_aff];
        REPEAT (POP_ASSUM MP_TAC) THEN MESON_TAC[]]]);;



let lemma_disjiont1a=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 n:num.
(complement_sets x V E v u n = complement_set {x,v})==>
((UNIV:real^3->bool) = aff {x,v} UNION (UNIONS {wedge_fan2 x V E v u i UNION wedge_fan3 x V E v u i | i IN (0..(n-1))}))`,
SUBGOAL_THEN `!x V E v u i. wedge_fan6 x V E v u i =wedge_fan2 x V E v u i UNION wedge_fan3 x V E v u i` ASSUME_TAC THENL
 [MESON_TAC[ lemma_disjiont_union];
  REPEAT GEN_TAC  THEN DISCH_TAC THEN 
  SUBGOAL_THEN `((UNIV:real^3->bool) = aff {x,v} UNION (UNIONS {wedge_fan6 x V E v u i | i IN (0..(n-1))}))` ASSUME_TAC
     THENL [ASM_MESON_TAC[ lemma_disjiont1];
            POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[]]]);;





(*******************[cor:W]*************************)

let disjiont_cor6dot1=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num. wedge_fan2 x V E v u i INTER wedge_fan3 x V E v u i={}`,
REPEAT GEN_TAC THEN REWRITE_TAC[wedge_fan2;wedge_fan3;FUN_EQ_THM] THEN GEN_TAC THEN 
REWRITE_TAC[INTER; EMPTY; IN_ELIM_THM] THEN
STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN(LABEL_TAC "a") THEN 
DISCH_THEN(LABEL_TAC "b") THEN
DISCH_THEN(LABEL_TAC "c") THEN
DISCH_THEN(LABEL_TAC "d") THEN
USE_THEN "a" MP_TAC THEN
USE_THEN "c" MP_TAC THEN
REAL_ARITH_TAC);;




let disjiont_cor6dot1a=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool)v:real^3 u:real^3 i:num j:num. 
(f_azim_fan x V E v u i <= f_azim_fan x V E v u j) ==> 
(wedge_fan2 x V E v u i INTER wedge_fan3 x V E v u j={})`,
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wedge_fan2;wedge_fan3;FUN_EQ_THM] THEN GEN_TAC THEN 
REWRITE_TAC[INTER; EMPTY; IN_ELIM_THM] THEN
STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN(LABEL_TAC "a") THEN 
DISCH_THEN(LABEL_TAC "b") THEN
DISCH_THEN(LABEL_TAC "c") THEN
DISCH_THEN(LABEL_TAC "d") 
THEN DISCH_THEN(LABEL_TAC "f") THEN
SUBGOAL_THEN `(f_azim_fan x V E v u j < f_azim_fan x V E v u i)` ASSUME_TAC
THENL
  [ASM_REWRITE_TAC[];
    POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC "g") THEN USE_THEN "a" MP_TAC THEN
USE_THEN "g" MP_TAC THEN REAL_ARITH_TAC]);;




let disjiont_cor6dot1b=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num j:num. 
(f_azim_fan x V E v u (j+1) <= f_azim_fan x V E v u i) ==> 
(wedge_fan2 x V E v u i INTER wedge_fan3 x V E v u j={})`,
REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[wedge_fan2;wedge_fan3;FUN_EQ_THM] THEN GEN_TAC THEN 
REWRITE_TAC[INTER; EMPTY; IN_ELIM_THM] THEN
STRIP_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN DISCH_THEN(LABEL_TAC "a") THEN 
DISCH_THEN(LABEL_TAC "b") THEN
DISCH_THEN(LABEL_TAC "c") THEN
DISCH_THEN(LABEL_TAC "d") 
THEN DISCH_THEN(LABEL_TAC "f") THEN
SUBGOAL_THEN `(f_azim_fan x V E v u i < f_azim_fan x V E v u (j+1))` ASSUME_TAC
THENL
  [ASM_REWRITE_TAC[];
    POP_ASSUM MP_TAC THEN DISCH_THEN(LABEL_TAC "g")
      THEN USE_THEN "a" MP_TAC THEN
      USE_THEN "g" MP_TAC THEN REAL_ARITH_TAC]);;



let disjiont_cor6dot1c= prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num j:num.
(f_azim_fan x V E v u (j+1) <= f_azim_fan x V E v u i)\/(f_azim_fan x V E v u i <= f_azim_fan x V E v u j) ==> 
(wedge_fan2 x V E v u i INTER wedge_fan3 x V E v u j={})`,
REPEAT GEN_TAC THEN STRIP_TAC 
THENL 
     [POP_ASSUM MP_TAC THEN MESON_TAC[disjiont_cor6dot1b];
      POP_ASSUM MP_TAC THEN MESON_TAC[disjiont_cor6dot1a]]);;





let disjiont1_cor6dot1 = prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num. wedge_fan3 x V E v u i INTER aff {x,v}={}`,
REPEAT GEN_TAC THEN REWRITE_TAC[wedge_fan3; INTER] THEN REWRITE_TAC[complement_set; FUN_EQ_THM; EMPTY] THEN
GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC
  THEN MESON_TAC[]);;


let disjiont2_cor6dot1=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num. wedge_fan3 x V E v u i INTER (aff {x,v} UNION wedge_fan2 x V E v u i)={}`,
REPEAT GEN_TAC THEN REWRITE_TAC[UNION_OVER_INTER] THEN SUBGOAL_THEN `wedge_fan3 x V E v u i INTER aff {x,v}={}` ASSUME_TAC
    THENL [MESON_TAC[disjiont1_cor6dot1];
          SUBGOAL_THEN `wedge_fan2 x V E v u i INTER wedge_fan3 x V E v u i={}` ASSUME_TAC
          THENL
              [MESON_TAC[disjiont_cor6dot1];
               SET_TAC[]]]);;


let disjiont2_cor6dot1a=prove(`!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num. 
((f_azim_fan x V E v u (j+1) <= f_azim_fan x V E v u i)\/(f_azim_fan x V E v u i <= f_azim_fan x V E v u j))==>
(wedge_fan3 x V E v u j INTER (aff {x,v} UNION wedge_fan2 x V E v u i)={})`,
REPEAT GEN_TAC THEN REWRITE_TAC[UNION_OVER_INTER] THEN DISCH_TAC THEN 
SUBGOAL_THEN `wedge_fan3 x V E v u j INTER aff {x,v}={}` ASSUME_TAC
    THENL 
       [MESON_TAC[disjiont1_cor6dot1];
        SUBGOAL_THEN `wedge_fan2 x V E v u i INTER wedge_fan3 x V E v u j={}` ASSUME_TAC
       THENL
          [ REPEAT(POP_ASSUM MP_TAC) THEN 
            DISCH_THEN (LABEL_TAC "a") THEN 
            DISCH_THEN(LABEL_TAC "b")  THEN
            USE_THEN "a" MP_TAC THEN MESON_TAC[disjiont_cor6dot1c];
                SET_TAC[]]]);;








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
(!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num.  ~( (power_map_points sigma_fan x V E v u i) IN aff {x, v})
==>
 aff_ge {x} {v , (power_map_points sigma_fan x V E v u i)} SUBSET   (wedge_fan2 x V E v u i)  UNION (aff {x, v}))   `,
DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
SUBGOAL_THEN ` wedge_fan2 x V E v u i = aff_gt {(x:real^3) , (v:real^3)} {power_map_points sigma_fan x V E (v:real^3) (u:real^3) (i:num)}` ASSUME_TAC THENL 
     [ASM_MESON_TAC[ wedge_fan2_equal_aff_gt];
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
(!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num. ~( (power_map_points sigma_fan x V E v u i) IN aff {x, v})
==>
( aff_ge {x} {v , (power_map_points sigma_fan x V E v u i)})  INTER (wedge_fan3 x V E v u i) = {} )`,
 
STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
SUBGOAL_THEN ` aff_ge {(x:real^3)} {(v:real^3) , (power_map_points sigma_fan x V E v (u:real^3) (i:num))} SUBSET   (wedge_fan2 x V E v u i)  UNION (aff {x, v})   ` ASSUME_TAC THENL
  [ASM_MESON_TAC[aff_ge_subset_wedge_fan2_union_aff];
   SUBGOAL_THEN `wedge_fan3 x V E v u i INTER (aff {x,v} UNION wedge_fan2 x V E v u i)={}` ASSUME_TAC
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
(f_azim_fan x V E v u (j+1) <= f_azim_fan x V E v u i)\/(f_azim_fan x V E v u i <= f_azim_fan x V E v u j))
==>
(!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num j:num. ~( (power_map_points sigma_fan x V E v u i) IN aff {x, v})
==>
(( aff_ge {x} {v , (power_map_points sigma_fan x V E v u i)}) INTER (wedge_fan3 x V E v u j) = {})) `,
STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
SUBGOAL_THEN ` aff_ge {(x:real^3)} {(v:real^3) , (power_map_points sigma_fan x (V:real^3->bool) (E:(real^3->bool)->bool) v (u:real^3) (i:num))} SUBSET   (wedge_fan2 x V E v u i)  UNION (aff {x, v})   ` ASSUME_TAC 
THENL
  [ASM_MESON_TAC[aff_ge_subset_wedge_fan2_union_aff];
   SUBGOAL_THEN `wedge_fan3 x (V:real^3->bool) (E:(real^3->bool)->bool) v u j INTER (aff {x,v} UNION wedge_fan2 x V E v u i)={}` ASSUME_TAC
     THENL
       [ASM_MESON_TAC[disjiont2_cor6dot1a];
        SET_TAC[]]]);;






(*************JGIYDLE*******************)

let rcone_fan = new_definition `rcone_fan  (x:real^3) (v:real^3) (h:real) = {y:real^3 | (y-x) dot (v-x) >(dist(y,x)*dist(v,x)*h)}`;;


let wedge_fane=new_definition`wedge_fane (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) (h:real)= wedge_fan3 x V E v u i INTER rcone_fan x v h`;;





let lemma_4dot31=prove(`(!x:real^3 v:real^3. aff {x , v} = {y:real^3| ?t1:real t2:real. (t1 + t2 = &1 )/\ (y = t1 % x + t2 % v )}) 
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. aff_gt {x , v} {w} = {y:real^3 | ?t1:real t2:real t3:real. (t3 > &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
/\ (!x:real^3 v:real^3 u:real^3 w:real^3 t1:real t2:real t3:real. ~(t3 = &0) /\ (t1 + t2 + t3 = &1)  ==> azim x v u w =
 azim x v u (t1 % x + t2 % v + t3 % w))
/\ (!x:real^3 v:real^3 u:real^3 w:real^3. {y:real^3 |  azim x v u w =
 azim x v u y}=aff_gt {x , v} {w})
/\ (!x:real^3 v:real^3 w:real^3. aff_ge {x} {v, w}={y:real^3 |  ?t1:real t2:real t3:real. (t2 >= &0)/\ (t3 >= &0) /\ (t1 + t2 + t3 = &1) /\ (y = t1 % x + t2 % v + t3 % w)})
/\ (!x:real^3  (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3 i:num j:num. 
(f_azim_fan x V E v u (j+1) <= f_azim_fan x V E v u i)\/(f_azim_fan x V E v u i <= f_azim_fan x V E v u j))
==>
(!x:real^3 (V:real^3->bool) (E:(real^3->bool)->bool) v:real^3 u:real^3  i:num j:num h:real. ~( (power_map_points sigma_fan x V E v u i) IN aff {x, v})
==>
(( aff_ge {x} {v , (power_map_points sigma_fan x V E  v u i)}) INTER (wedge_fane x V E v u j h) = {})) `,

STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[wedge_fane] THEN
SUBGOAL_THEN `(( aff_ge {(x:real^3)} {(v:real^3) , (power_map_points sigma_fan x (V:real^3->bool) (E:(real^3->bool)->bool) v (u:real^3) (i:num))}) INTER (wedge_fan3 (x:real^3) V E v u (j:num)) = {})` ASSUME_TAC  
THENL
  [ASM_MESON_TAC[disjiont_aff_ge_wedge_fan3a];
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









let w_dart_in_ball=new_definition`w_dart_in_ball  (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (v:real^3) (u:real^3) (i:num) (h:real) = (ballnorm_fan x) INTER (wedge_fane x V E v u i h)`;;


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


