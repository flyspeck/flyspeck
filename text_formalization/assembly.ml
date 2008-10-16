(* Main estimate file*)
(* Author: PHAN HOANG CHON *)
(*========================================================*)
(*
needs "database_more.ml";;
needs "definitions_kepler.ml";;
needs "Multivariate/convex.ml";;
needs "geomdetail.ml";;              (* Writen by Nguyen Quang TRuong   *)
*)
(*========================================================*)
(* These definitions are defined by other authors*)
(*========================================================*)
(*Some constant*)

(*arctan2 function is defined in definition_kepler.ml*)

let delta_tet = kepler_def (`delta_tet = sqrt8 * atn2(&5, sqrt2)`);;

let delta_oct = kepler_def (`delta_oct = (( &3* pi_rt18 - delta_tet)*( &1 / &2 ))`);;

(*========================================================*)

let lambda_v = kepler_def (`lambda_v = (-- &4)* delta_oct `);;

let lambda_s = kepler_def (`lambda_s = (&1)/(&3) `);;

let lambda_oct = kepler_def (`lambda_oct = (lambda_v , lambda_s) `);;

(*========================================================*)

let open_ball = new_definition `open_ball (x:real^3) (r:real)= { y | norm(y-x)< r }`;;

(*========================================================*)

(* There is a mistake in this definition. For example: let d={x,y,z,t} be a quarter with 2*t0<dist(x,y)<=sqrt8
and dist(z,t)=2*t0, then diagonal {z ,t} d s is true, that means {z,t} is diagonal of d. But here {x,y} is really
diagonal of d.

let diagonal = new_definition ` diagonal dgcheo d s = ( quarter d s /\
                 ( ? x y. x IN d /\ y IN d /\ { x, y } = dgcheo /\ d3 x y >= &2 * t0 ))`;;
*)

(*========================================================*)

let diag = new_definition ` diag d q s = ( quarter q s /\
                 ( ? x y. 
                      ! v1 v2.
                           x IN q /\ y IN q /\
                           v1 IN q /\ v2 IN q /\
                           { x, y } = d /\ d3 x y >= &2 * t0 /\
                            d3 x y >= d3 v1 v2 ))`;;

let find_diagonal = new_definition ` find_diagonal q s:real^3->bool = @{x, y}. {x , y} SUBSET q /\ diag {x , y} q s `;;

let find_dia = new_definition ` find_dia q (s:real^3->bool) = 
                                   let d = find_diagonal q s in
                                   @(u,v). u IN d /\ v IN d /\ ~( u = v ) `;;

let anchor = new_definition ` anchor (v:real^3) v1 v2 = ( d3 v1 v2 <= sqrt ( &8 ) /\
               d3 v1 v2 >= &2 * t0 /\ d3 v v1 <= &2 * t0 /\ d3 v v2 <= &2 * t0 )`;;

(* Definition 7.20 =============================================*)

let context = new_definition ` context (v , w) s (p:num, r) = ( 
                    CARD { d | diag { v , w } d s } = p /\
                    CARD { t | &2 * t0 <= d3 v w /\ anchor t v w } = (p + r ))`;;

let cotext = new_definition ` cotext (v , w) (s:real^3->bool) = @( (p:num) , (r:num) ). 
                                           CARD { d | diag { v , w } d s } = p /\ 
                                           CARD { t | &2 * t0 <= d3 v w /\ anchor t v w } = (p + r )`;;
                    
(* Definition 7.21 =============================================*)

let VC1 = new_definition ` VC1 v s d =  VC v d INTER conv s `;;
let VCt = new_definition ` VCt x t s d 
                        = VC1 x s d INTER open_ball x t `;;

(* Definition 7.22 =============================================*)

let sv = new_definition ` sv x p d = lambda_v * vol(VC1 x p d) + lambda_s * solid x (conv0 p) `;;

let gamma = new_definition ` gamma (v1 , v2 , v3 , v4) d = 
                 ( &1 / &4 ) * ( sv v1 { v1 , v2 , v3 , v4 } d +
                                 sv v2 { v1 , v2 , v3 , v4 } d +
                                 sv v3 { v1 , v2 , v3 , v4 } d +
                                 sv v4 { v1 , v2 , v3 , v4 } d )`;;

let volan = new_definition ` volan v0 (v0 , v1, v2, v3 ) =
                let x01 = dist(v0,v1) pow 2 in 
                let x02 = dist(v0,v2) pow 2 in
                let x03 = dist(v0,v3) pow 2 in
                let x12 = dist(v1,v2) pow 2 in 
                let x13 = dist(v1,v3) pow 2 in
                let x23 = dist(v2,v3) pow 2 in
                  ( x01 * ( x02 + x12 - x01 ) * ( chi_x x23 x13 x03 x01 x02 x12 ) ) /
                  ( &48 * (ups_x x01 x02 x12) * sqrt( delta_x x01 x02 x03 x23 x13 x12 )) + 
                  ( x01 * ( x03 + x13 - x01 ) * ( chi_x x23 x12 x02 x01 x03 x13 ) ) /
                  ( &48 * (ups_x x01 x03 x13) * sqrt( delta_x x01 x02 x03 x23 x13 x12 )) +
                  ( x02 * ( x01 + x12 - x02 ) * ( chi_x x13 x23 x03 x02 x01 x12 ) ) /
                  ( &48 * (ups_x x02 x01 x12) * sqrt( delta_x x01 x02 x03 x23 x13 x12 )) +
                  ( x01 * ( x03 + x23 - x02 ) * ( chi_x x13 x12 x01 x02 x03 x23 ) ) /
                  ( &48 * (ups_x x02 x03 x23) * sqrt( delta_x x01 x02 x03 x23 x13 x12 )) +
                  ( x02 * ( x01 + x13 - x03 ) * ( chi_x x12 x23 x02 x03 x01 x13 ) ) /
                  ( &48 * (ups_x x03 x01 x13) * sqrt( delta_x x01 x02 x03 x23 x13 x12 )) +
                  ( x02 * ( x02 + x23 - x03 ) * ( chi_x x12 x13 x01 x03 x02 x23 ) ) /
                  ( &48 * (ups_x x03 x02 x23) * sqrt( delta_x x01 x02 x03 x23 x13 x12 )) `;;

let svan =new_definition ` svan v0 ( v0 , v1, v2, v3) = 
                    lambda_v * volan v0 ( v0 , v1, v2, v3) + 
                    lambda_s * solid v0 ( conv0 { v0 , v1, v2, v3}) `;;
                  
(* Definition 7.23 =================================================*)

let eta_pos = new_definition ` eta_pos (q:real^3->bool) (s:real^3->bool) = 
                                   let d = find_diagonal q s in
                                   let f1 = d UNION ( @{u}. ( q DIFF d ) u ) in 
                                   let f2 = d UNION ( @{v}. ( q DIFF f1) v ) in    
                                   ( max_real ( radV f1 ) ( radV f2) )`;;
                            
(* The definition 7.24 =============================================*)

let sv0 = new_definition ` sv0 v s d = sovo v (VCt v t0 s d) lambda_oct `;;

let v_hat = new_definition `v_hat v q s = if ( quarter q s ) /\ ( v IN find_diagonal q s ) 
                                      then ( @u. u IN (find_diagonal q s DIFF {v} ))
                                      else v `;;

let sigma = new_definition ` sigma v0 ( v0 , v1 , v2, v3 ) ( s:real^3->bool ) = 
                             let q = { v0 , v1 , v2 , v3 } in
                             if ( quasi_reg_tet q s ) then  
                                          if  radV q  < sqrt2 then gamma ( v0 , v1 , v2, v3 ) s
                                          else  svan v0 ( v0 , v1 , v2, v3 )
                             else   if ( eta_pos q s ) < sqrt2  then 
                                                 if ( cotext ( find_dia q s ) s = (1,1) ) \/( cotext ( find_dia q s ) s = (4,0) ) then 
                                                                            gamma (v0 , v1 , v2, v3 ) s 
                                                  else gamma ( v0 , v1 , v2, v3 ) s  + ( &1 / &2 )* ( ( sv0 v0 q s ) - ( sv0 ( v_hat v0 q s ) q s ))
                                   else  if ( cotext ( find_dia q s ) s = (1,1) ) then svan v0 ( v0 , v1, v2, v3 )
                                          else ( if ( cotext ( find_dia q s ) s = (4,0) ) then 
                                                     ( &1 / &2 )* ( ( svan v0 ( v0 , v1, v2, v3 )) + ( svan ( v_hat v0 q s ) ( v0 , v1, v2, v3 )))
                                                else ( &1 / &2 )* ( ( svan v0 ( v0 , v1, v2, v3 )) + ( svan ( v_hat v0 q s ) ( v0 , v1, v2, v3 ))) + 
                                                     ( &1 / &2 )* ( ( sv0 v0 q s - sv0 ( v_hat v0 q s) q s ))) `;; 

let A_1 = new_definition ` A_1 v0 ( v0 , v1 , v2 , v3 ) (s:real^3->bool) = 
                                      let q = { v0 , v1 , v2 , v3 } in
                                      -- vol( VC1 v0 q s ) + (( solid v0 q )/ ( &3 * delta_oct )) 
                                      + (( sigma v0 ( v0 , v1 , v2, v3 ) s ) / (&4 * delta_oct )) `;;
(*=====================================================================*)
(* this definition is writen by anhtamct ==============================*)
let ball3_lambda = new_definition ` ball3_lambda (x:real^3) (r:real) (Lambda:real^3 -> bool) = 
                                            ((open_ball x r ) INTER ( UNIONS ( IMAGE (\v. open_ball v (&1) ) Lambda ) ))`;; 
let truncated_packing = new_definition ` truncated_packing x r Lambda = Lambda INTER (ball3_lambda x r Lambda) `;;
(*=====================================================================*)
(* these definition are writen by Hoang Le Truong =====================*)
let graph = new_definition `graph E <=> (!e. E e ==> (e HAS_SIZE 2))`;;
let fan1 = new_definition`fan1(x,V,E):bool <=> FINITE V /\ ~(V SUBSET {}) `;;
let fan2 = new_definition`fan2(x,V,E):bool <=> ~(x IN V)`;;

let fan3=new_definition`fan3(x,V,E):bool <=> (!v. (v IN V) ==> cyclic_set {w | {v,w} IN E } x v)`;;

let fan4 = new_definition`fan4(x,V,E):bool<=> (!e. (e IN E) ==> (aff_gt {x} e INTER V={}))`;;

let fan5 = new_definition`fan5(x,V,E):bool<=> (!e f. (e IN E)/\ (f IN E) /\ ~(e=f) ==> (aff_gt {x} e INTER aff_gt {x} f ={}))`;;
let fan = new_definition`fan(x,V,E)<=> ((UNIONS E) SUBSET V) /\ graph(E)/\ fan1(x,V,E)/\ fan2(x,V,E)/\ fan3(x,V,E)/\ fan4 (x,V,E) /\ fan5(x,V,E)`;;
let X= new_definition`X fan(x,V,E)={v | ?e. (E e)/\(v IN aff_ge {x} e)}`;;
let Y= new_definition`Y fan(x,V,E)={v:real^3 | ?e. (E e)/\(~(v IN aff_ge {x} e))}`;;
(*=====================================================================*)
(* Definition 8.9 =====================================================*)
let tru_pack =new_definition ` tru_pack (v:real^3) (r:real) (s:real^3->bool) =
                                  { x | center_pac s v /\ x IN s /\ x IN open_ball v r }`;;
let v_std = new_definition ` v_std (s:real^3->bool) (v0:real^3) = ( tru_pack v0 ( &2 * t0 ) s ) DIFF {v0}`;;
let e_std = new_definition ` e_std (s:real^3->bool) (v0:real^3) =
                         { { u , v } | u IN (tru_pack v0 ( &2 * t0 ) s ) DIFF {v0}  /\ 
                                   v IN (tru_pack v0 ( &2 * t0 ) s ) DIFF {v0}  /\ 
                                  ~(u = v) /\ d3 u v <= ( &2 * t0 ) }`;;
(*=====================================================================*)
(* prove lemma 8.30 *)
(*=====================================================================*)
let in_lemma2 = REWRITE_CONV[IN_ELIM_THM]
  `e IN {{u, v} | u IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
               v IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
               ~(u = v) /\
               d3 u v <= &2 * t0}`;;

let in_inv = prove (`{{u, v} | u IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
           v IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
           ~(u = v) /\
           d3 u v <= &2 * t0} e <=> e IN {{u, v} | u IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
           v IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
           ~(u = v) /\
           d3 u v <= &2 * t0}`,SET_TAC[]);;

let lemma_graph = prove(`center_pac (s:real^3->bool) (v0:real^3) ==> graph (e_std s v0)`, REWRITE_TAC[e_std;tru_pack;graph] 
                                        THEN DISCH_TAC THEN ASM_REWRITE_TAC[] 
                                        THEN REWRITE_TAC[SET_RULE `{x | x IN s /\ x IN open_ball v0 (&2 * t0)}= s INTER open_ball v0 (&2 * t0)`]
                                        THEN GEN_TAC THEN REWRITE_TAC[in_inv] THEN REWRITE_TAC[in_lemma2]
                                        THEN REWRITE_TAC[ARITH_RULE `2 = SUC (SUC 0)`;HAS_SIZE_CLAUSES]THEN REPEAT STRIP_TAC
                                        THEN EXISTS_TAC`u:real^3` THEN EXISTS_TAC`{v:real^3}`
                                        THEN ASM_REWRITE_TAC[IN_INSERT;NOT_IN_EMPTY] THEN EXISTS_TAC `v:real^3` THEN EXISTS_TAC `{}:real^3->bool`
                                        THEN ASM_REWRITE_TAC[IN_INSERT;NOT_IN_EMPTY]);;

(*=====================================================================*)
