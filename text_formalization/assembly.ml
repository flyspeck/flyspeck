(* Main estimate file*)
(* Author: PHAN HOANG CHON *)
(*========================================================*)

needs "database_more.ml";;
needs "definitions_kepler.ml";;
(* removed convex.ml by thales, not compatible with other loads *)
(* needs "Multivariate/convex.ml";; *)
needs "geomdetail.ml";;              (* Writen by Nguyen Quang TRuong   *)

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

(* thales, nov 11. anchor is already defined in geomdetail.ml *)
let anchor_alt = new_definition ` anchor_alt (v:real^3) v1 v2 = ( d3 v1 v2 <= sqrt ( &8 ) /\
               d3 v1 v2 >= &2 * t0 /\ d3 v v1 <= &2 * t0 /\ d3 v v2 <= &2 * t0 )`;;

(* Definition 7.20 =============================================*)

let context = new_definition ` context (v , w) s (p:num, r) = ( 
                    CARD { d | diag { v , w } d s } = p /\
                    CARD { t | &2 * t0 <= d3 v w /\ anchor_alt t v w } = (p + r ))`;;

let cotext = new_definition ` cotext (v , w) (s:real^3->bool) = @( (p:num) , (r:num) ). 
                                           CARD { d | diag { v , w } d s } = p /\ 
                                           CARD { t | &2 * t0 <= d3 v w /\ anchor_alt t v w } = (p + r )`;;
                    
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
(* Definition 26 in collection_geom file ==============================*)
let condC = new_definition ` condC (M13:real) (m12:real) (m14:real) (M24:real) (m34:real) (m23:real) =
                         (( m12 + m23 >= M13 ) /\ ( m14 + m34 >= M13 ) /\ ( m12 + m14 > M24 ) /\ ( m23 + m34 > M24 ) /\
                         ( delta_x (M13 pow 2) (m12 pow 2) (m14 pow 2) (M24 pow 2) (m34 pow 2) (m23 pow 2) >= &0 ))` ;;
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

let uni_lemma1 = prove( ` UNIONS
 {{u, v} | u IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
           v IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
           ~(u = v) /\
           d3 u v <= &2 * t0} =UNIONS
 {{u1, v1} | u1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
           v1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
           ~(u1 = v1) /\
           d3 u1 v1 <= &2 * t0}`,SET_TAC[]);;

let in_lemma1 = REWRITE_CONV[IN_ELIM_THM]
`u IN
      {{u1, v1} | u1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                  v1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                  ~(u1 = v1) /\
                  d3 u1 v1 <= &2 * t0}`;;

let in_lemma = ONCE_REWRITE_CONV[IN_ELIM_THM]
`x IN
     {y | ?u. u IN
              {{u1, v1} | u1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                          v1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                          ~(u1 = v1) /\
                          d3 u1 v1 <= &2 * t0} /\
              y IN u}`;;

let exist_lemma = prove(` (?u. (?u1 v1.
           (u1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
            v1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
            ~(u1 = v1) /\
            d3 u1 v1 <= &2 * t0) /\
           u = {u1, v1}) /\
      x IN u) <=> (?u1 v1.
           (u1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
            v1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
            ~(u1 = v1) /\
            d3 u1 v1 <= &2 * t0 /\
           x IN { u1, v1 }))`, MESON_TAC[]);;

let cha_lemma1 = prove (`{x | ?u. u IN
              {{u1, v1} | u1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                          v1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                          ~(u1 = v1) /\
                          d3 u1 v1 <= &2 * t0} /\
              x IN u} = {y | ?u. u IN
              {{u1, v1} | u1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                          v1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                          ~(u1 = v1) /\
                          d3 u1 v1 <= &2 * t0} /\
              y IN u}`,SET_TAC[]);;

let exist_lemma1 = prove(` (?u1 v1.
      u1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
      v1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
      ~(u1 = v1) /\
      d3 u1 v1 <= &2 * t0 /\
      x = u1 \/
      u1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
      v1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
      ~(u1 = v1) /\
      d3 u1 v1 <= &2 * t0 /\
      x = v1) <=> 
  ( ?v1.
      x IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
      v1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
      ~(x = v1) /\
      d3 x v1 <= &2 * t0 ) \/
  ( ?u1.
      u1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
      x IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
      ~(u1 = x) /\
      d3 u1 x <= &2 * t0 )`,MESON_TAC[]);;

let unions_lemma = prove (`!(v0:real^3) (s:real^3->bool). center_pac (s:real^3->bool) (v0:real^3) ==> UNIONS (e_std s v0) SUBSET v_std s v0`, 
                                     REPEAT GEN_TAC THEN REWRITE_TAC[e_std;v_std;tru_pack]
                                     THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN 
                                     REWRITE_TAC[SET_RULE` {x | x IN s /\ x IN open_ball v0 (&2 * t0)}= s INTER open_ball v0 (&2 * t0)`] THEN
                                     ONCE_REWRITE_TAC[uni_lemma1] THEN REWRITE_TAC[SUBSET;UNIONS] THEN ONCE_REWRITE_TAC[cha_lemma1] THEN
                                     ONCE_REWRITE_TAC[in_lemma] THEN GEN_TAC THEN ONCE_REWRITE_TAC[in_lemma1] THEN REWRITE_TAC[exist_lemma] THEN
                                     REWRITE_TAC[SET_RULE ` x IN {u1 , v1} <=> x = u1 \/ x = v1`] THEN 
                                     REWRITE_TAC[TAUT ` u1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                                          v1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                                        ~(u1 = v1) /\
                                          d3 u1 v1 <= &2 * t0 /\
                                          (x = u1 \/ x = v1) <=> ( u1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                                           v1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                                         ~(u1 = v1) /\
                                          d3 u1 v1 <= &2 * t0 /\
                                          x = u1) \/ ( u1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                                           v1 IN s INTER open_ball v0 (&2 * t0) DIFF {v0} /\
                                        ~(u1 = v1) /\
                                         d3 u1 v1 <= &2 * t0 /\
                                         x = v1 )`] THEN 
                                     REWRITE_TAC[exist_lemma1] THEN STRIP_TAC);;

let lemma7_1 = new_axiom `!(v0:real^3) (s:real^3->bool) r:real. center_pac (s:real^3->bool) (v0:real^3) ==> 
                           FINITE (tru_pack v0 r s )`;;

let fini_lemma = prove(` FINITE (tru_pack v0 (&2 * t0) s)
                          ==> FINITE (tru_pack v0 (&2 * t0) s DIFF {v0})`, REWRITE_TAC[FINITE_DIFF]);;

let infi_lemma2 = prove(`center_pac s v0 ==> FINITE (tru_pack v0 (&2 * t0) s) `, REWRITE_TAC[lemma7_1]);;

let fini_lemma1 = prove(`!(v0:real^3) (s:real^3->bool). center_pac s v0 ==> FINITE ( v_std s v0 )`,
                       REPEAT GEN_TAC THEN REWRITE_TAC[v_std] THEN DISCH_TAC THEN
                       MATCH_MP_TAC ( fini_lemma) THEN 
                       UNDISCH_TAC `center_pac (s:real^3->bool) (v0:real^3)` THEN REWRITE_TAC[infi_lemma2]);;

let fan1_lemma = prove(`!(v0:real^3) (s:real^3->bool). center_pac (s:real^3->bool) (v0:real^3) /\ ~( v_std s v0 = {}) ==> 
                       fan1 (v0 , v_std s v0 , e_std s v0 )` , REPEAT GEN_TAC THEN REWRITE_TAC[fan1] THEN 
                       REWRITE_TAC[TAUT `center_pac s v0 /\ ~(v_std s v0 = {} ) ==> FINITE ( v_std s v0 ) /\ ~(v_std s v0 SUBSET {}) <=> 
                                    ( center_pac s v0 /\ ~( v_std s v0 = {}) ==> FINITE ( v_std s v0 ) ) /\ 
                                    ( center_pac s v0 /\ ~( v_std s v0 = {}) ==> ~(v_std s v0 SUBSET {}))`] THEN
                       REWRITE_TAC[SET_RULE ` ~( v_std s v0 SUBSET {}) <=> ~( v_std s v0 = {})`] THEN
                       MESON_TAC[fini_lemma1]);;

let fan2_lemma = prove(`!(v0:real^3) (s:real^3->bool). center_pac s v0 ==> fan2 (v0,v_std s v0,e_std s v0 )`,
                       REPEAT GEN_TAC THEN REWRITE_TAC[fan2;v_std;DIFF] THEN SET_TAC[]);;

let lemmaf3 = prove(`{v, w} IN
     {{x, y} | x IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
               y IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
               ~(x = y) /\
               d3 x y <= &2 * t0} <=>
     (?x y.
          (x IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
           y IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
           ~(x = y) /\
           d3 x y <= &2 * t0) /\
          {v, w} = {x, y})`, REWRITE_TAC[IN_ELIM_THM]);;

let lemma_subset = prove ( `{w | ?x y.
              (x IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
               y IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
               ~(x = y) /\
               d3 x y <= &2 * t0) /\
              {v, w} = {x, y}} SUBSET tru_pack v0 (&2 * t0) s DIFF {v0}`, SET_TAC[]);;

let lemmaf32 = prove (` FINITE (tru_pack v0 (&2 * t0) s DIFF {v0})
 ==> FINITE
     {w | ?x y.
              (x IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
               y IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
               ~(x = y) /\
               d3 x y <= &2 * t0) /\
              {v, w} = {x, y}} <=> ( FINITE (tru_pack v0 (&2 * t0) s DIFF {v0}) /\ {w | ?x y.
              (x IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
               y IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
               ~(x = y) /\
               d3 x y <= &2 * t0) /\
              {v, w} = {x, y}} SUBSET
     tru_pack v0 (&2 * t0) s DIFF {v0} )
 ==> FINITE
     {w | ?x y.
              (x IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
               y IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
               ~(x = y) /\
               d3 x y <= &2 * t0) /\
              {v, w} = {x, y}}`, MESON_TAC[lemma_subset]);;

let lemmaf33 = prove(` FINITE (tru_pack v0 (&2 * t0) s DIFF {v0})
     ==> FINITE
         {w | ?x y.
                  (x IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
                   y IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
                   ~(x = y) /\
                   d3 x y <= &2 * t0) /\
                  {v, w} = {x, y}}`, REWRITE_TAC[lemmaf32] THEN REWRITE_TAC[FINITE_SUBSET]);;

let lemmaf34 = prove (` condC (#2.6) (&2) (&2) (#2.6) (&2) (&2)`, REWRITE_TAC[condC;delta_x] THEN REAL_ARITH_TAC);;

(* prove lemma have_not_prove*)

let lemma_c = REWRITE_CONV[IN_ELIM_THM]`&1 / (h + &1) % p + h / (h + &1) % v IN
                                       {w | ?a b. &0 <= a /\ &0 <= b /\ a + b = &1 /\ w = a % p + b % v}`;;

let lemma_2 = REWRITE_CONV[IN_ELIM_THM]`&1 / (h + &1) % p + h / (h + &1) % v IN
                                        {w | ?a b. &0 <= a /\ &0 <= b /\ a + b = &1 /\ w = a % q + b % v0}`;;

let lemma_c1 = prove (` &0 <= h ==> &0 <= &1 / (h + &1)`, DISCH_TAC THEN MATCH_MP_TAC (REAL_LE_DIV) THEN UNDISCH_TAC `&0 <= h`
                 THEN REWRITE_TAC[MESON[]` &0 <= h ==> &0 <= &1 /\ &0 <= h + &1 <=> ( &0 <= h ==> &0 <= &1 ) /\ (&0 <= h ==> &0 <= h + &1 )`]
                 THEN REAL_ARITH_TAC);;

let lemma_c11 = prove (`&0 < &1 / ( h + &1) ==> &0 <= &1 / (h + &1) `, REAL_ARITH_TAC);;

let lemma_c111 = prove (`h >= &0 ==> &0 <= &1 / (h + &1)`, DISCH_TAC THEN MATCH_MP_TAC (lemma_c1)
                           THEN UNDISCH_TAC `h:real >= &0` THEN REAL_ARITH_TAC);;

let lemma_ch = prove (` &0 <= h ==> &0 <= h / (h + &1)`, DISCH_TAC THEN MATCH_MP_TAC (REAL_LE_DIV) THEN UNDISCH_TAC `&0 <= h`
                 THEN REWRITE_TAC[MESON[]` &0 <= h ==> &0 <= h /\ &0 <= h + &1 <=> ( &0 <= h ==> &0 <= h ) /\ (&0 <= h ==> &0 <= h + &1 )`]
                 THEN REAL_ARITH_TAC);;

let lemma_ch1 = prove (`&0 < h / ( h + &1) ==> &0 <= h / (h + &1) `, REAL_ARITH_TAC);;

let lemma_ch11 = prove (`h >= &0 ==> &0 <= h / (h + &1)`, DISCH_TAC THEN MATCH_MP_TAC (lemma_ch)
                           THEN UNDISCH_TAC `h:real >= &0` THEN REAL_ARITH_TAC);;

let lemma_1 = prove (` h >= &0 ==> &1 / (h + &1) + h / (h + &1) = &1`, STRIP_TAC THEN
                       REWRITE_TAC[REAL_ARITH `&1 / (h + &1) + h / (h + &1) = (h + &1)/ (h + &1)`] THEN
                       MATCH_MP_TAC (REAL_DIV_REFL) THEN UNDISCH_TAC `h >= &0` THEN REAL_ARITH_TAC);;

let le1_diag_trape = prove (` p:real^3 = q + (h:real) % (v0 - v) /\ h >= &0 
                                ==> &1 / (h + &1) % p + h / (h + &1) % v IN {w | ?a b. &0 <= a /\ &0 <= b /\ a + b = &1 /\ w = a % p + b % v}`,
                             REWRITE_TAC[lemma_c]THEN STRIP_TAC THEN EXISTS_TAC ` &1 / (h+ &1)` THEN EXISTS_TAC ` h:real / (h+ &1)` THEN
                             UNDISCH_TAC `h:real >= &0` THEN 
                             REWRITE_TAC[MESON[] ` h >= &0
                                      ==> &0 <= &1 / (h + &1) /\
                                         &0 <= h / (h + &1) /\
                                         &1 / (h + &1) + h / (h + &1) = &1 /\
                                         &1 / (h + &1) % p + h / (h + &1) % v =
                                         &1 / (h + &1) % p + h / (h + &1) % v <=> 
                                         ( h >= &0 ==> &0 <= &1 / (h + &1) ) /\
                                         ( h >= &0 ==> &0 <= h / (h + &1) ) /\
                                         ( h >= &0 ==> &1 / (h + &1) + h / (h + &1) = &1 ) /\
                                         ( h >= &0 ==> &1 / (h + &1) % p + h / (h + &1) % v =
                                            &1 / (h + &1) % p + h / (h + &1) % v )`] THEN
                             REWRITE_TAC[lemma_c111;lemma_ch11;lemma_1]);;

let diag_trape = prove (` !(p:real^3) (q:real^3) (v0:real^3) (v:real^3) (h:real). p = q + h % (v0 - v) /\ h >= &0 ==> 
                             ~(conv {p, v} INTER conv {q, v0} = {})`, REPEAT GEN_TAC THEN DISCH_TAC THEN
                             REWRITE_TAC[SET_RULE ` ~(conv {p, v} INTER conv {q, v0} = {}) <=> ? x. x IN conv {p, v} /\ x IN conv {q, v0}`] THEN
                             EXISTS_TAC ` (&1/(h + &1)) % (p:real^3) + ((h:real)/(h + &1)) % (v:real^3)` THEN
                             UNDISCH_TAC `p:real^3 = q + h % (v0 - v) /\ h >= &0 ` THEN REWRITE_TAC[CONV_SET2] THEN
                             REWRITE_TAC[MESON[] ` p = q + h % (v0 - v) /\ h >= &0
                                   ==> &1 / (h + &1) % p + h / (h + &1) % v IN
                                    {w | ?a b. &0 <= a /\ &0 <= b /\ a + b = &1 /\ w = a % p + b % v} /\
                                    &1 / (h + &1) % p + h / (h + &1) % v IN
                                    {w | ?a b. &0 <= a /\ &0 <= b /\ a + b = &1 /\ w = a % q + b % v0} <=> 
                                   ( p = q + h % (v0 - v) /\ h >= &0
                                 ==> &1 / (h + &1) % p + h / (h + &1) % v IN
                                     {w | ?a b. &0 <= a /\ &0 <= b /\ a + b = &1 /\ w = a % p + b % v} ) /\ 
                                   ( p = q + h % (v0 - v) /\ h >= &0
                                 ==> &1 / (h + &1) % p + h / (h + &1) % v IN
                                     {w | ?a b. &0 <= a /\ &0 <= b /\ a + b = &1 /\ w = a % q + b % v0} )`] THEN
                             REWRITE_TAC[le1_diag_trape] THEN REWRITE_TAC[lemma_2] THEN STRIP_TAC THEN
                             EXISTS_TAC ` &1 / (h+ &1)` THEN EXISTS_TAC ` h:real / (h+ &1)` THEN UNDISCH_TAC `h >= &0` THEN
                             REWRITE_TAC[MESON[] ` h >= &0
                                          ==> &0 <= &1 / (h + &1) /\
                                             &0 <= h / (h + &1) /\
                                             &1 / (h + &1) + h / (h + &1) = &1 /\
                                             &1 / (h + &1) % p + h / (h + &1) % v =
                                             &1 / (h + &1) % q + h / (h + &1) % v0 <=> 
                                             ( h >= &0 ==> &0 <= &1 / (h + &1) ) /\
                                             ( h >= &0 ==> &0 <= h / (h + &1) ) /\
                                             ( h >= &0 ==> &1 / (h + &1) + h / (h + &1) = &1 ) /\
                                             ( h >= &0 ==> &1 / (h + &1) % p + h / (h + &1) % v =
                                                &1 / (h + &1) % q + h / (h + &1) % v0 )`] THEN
                              REWRITE_TAC[lemma_c111; lemma_ch11; lemma_1] THEN DISCH_TAC THEN 
                              REWRITE_TAC[VECTOR_ARITH `&1 / (h + &1) % p + h / (h + &1) % v = &1 / (h + &1) % q + h / (h + &1) % v0 <=>
                               &1 / (h + &1) % p = &1 / (h + &1) % q + h / (h + &1) % v0 - ( h / (h + &1) % v )`] THEN
                              REWRITE_TAC[VECTOR_ARITH `&1 / (h + &1) % p = &1 / (h + &1) % q + h / (h + &1) % v0 - h / (h + &1) % v
                                <=> &1 / (h + &1) % p = &1 / (h + &1) % q + h / (h + &1) % (v0 - v)`] THEN ASM_REWRITE_TAC[] THEN
                              VECTOR_ARITH_TAC ) ;;

let inv_diag = prove(`!(p:real^3) (q:real^3) (v0:real^3) (v:real^3) (h:real). p = q + h % (v0 - v) /\ conv {p, v} INTER conv {q, v0} = {} ==> ~(h >= &0)`,
                      REWRITE_TAC[TAUT `p = q + h % (v0 - v) /\ conv {p, v} INTER conv {q, v0} = {}
                          ==> ~(h >= &0) <=> p = q + h % (v0 - v) ==> ( conv {p, v} INTER conv {q, v0} = {} ==> ~(h >= &0) )`] THEN
                      REWRITE_TAC[TAUT ` conv {p, v} INTER conv {q, v0} = {}
                          ==> ~(h >= &0) <=> ( h >= &0 ==> ~(conv {p, v} INTER conv {q, v0} = {}))`] THEN
                      REWRITE_TAC[TAUT `p = q + h % (v0 - v)==> h >= &0
                          ==> ~(conv {p, v} INTER conv {q, v0} = {}) <=> ( p = q + h % (v0 - v) /\ h >= &0 ) ==> ~(conv {p, v} INTER conv {q, v0} = {})`] THEN
                      REWRITE_TAC[diag_trape]);;

let vec_le = prove (` (h:real) % ( v0:real^3 - v ) = -- h % (v - v0)`, VECTOR_ARITH_TAC);;


let diag_trape1 = prove ( ` !(p:real^3) (q:real^3) (v0:real^3) (v:real^3) (h:real). p = q + h % (v0 - v) /\ h <= &0 ==> 
                             ~(conv {p, v0} INTER conv {q, v} = {})`, REWRITE_TAC[REAL_ARITH ` h <= &0 <=> -- h >= &0`] THEN
                              ONCE_REWRITE_TAC[vec_le] THEN REWRITE_TAC[diag_trape]);;

let inv_diag1 = prove(`!(p:real^3) (q:real^3) (v0:real^3) (v:real^3) (h:real). p = q + h % (v0 - v) /\ conv {p, v0} INTER conv {q, v} = {} ==> ~(h <= &0)`,
                      REWRITE_TAC[TAUT `p = q + h % (v0 - v) /\ conv {p, v0} INTER conv {q, v} = {}
                          ==> ~(h <= &0) <=> p = q + h % (v0 - v) ==> ( conv {p, v0} INTER conv {q, v} = {} ==> ~(h <= &0) )`] THEN
                      REWRITE_TAC[TAUT ` conv {p, v0} INTER conv {q, v} = {}
                          ==> ~(h <= &0) <=> ( h <= &0 ==> ~(conv {p, v0} INTER conv {q, v} = {}))`] THEN
                      REWRITE_TAC[TAUT `p = q + h % (v0 - v)==> h <= &0
                          ==> ~(conv {p, v0} INTER conv {q, v} = {}) <=> ( p = q + h % (v0 - v) /\ h <= &0 ) ==> ~(conv {p, v0} INTER conv {q, v} = {})`] THEN
                      REWRITE_TAC[diag_trape1]);;


let lemma_3_4 = new_axiom (` !(v1:real^3) (v2:real^3) (v3:real^3) (v4:real^3).
                             !(m12:real) (m23:real) (m34:real) (m14:real) (M13:real) (M24:real).  
                               d3 v1 v2 >= m12 /\
                               d3 v2 v3 >= m23 /\
                               d3 v3 v4 >= m34 /\
                               d3 v4 v1 >= m14 /\
                               d3 v1 v3 <  M13 /\
                               d3 v2 v4 <= M24 /\
                               condC M13 m12 m14 M24 m34 m23 
                            ==> conv {v1 , v3} INTER conv {v2 , v4} = {}`);;

let lemma_3_4_c = new_axiom (` !(p:real^3) (q:real^3) (v:real^3) (v0:real^3).
                               d3 p q >= m12 /\
                               d3 q v >= m23 /\
                               d3 v v0 >= m34 /\
                               d3 v0 p >= m14 /\
                               d3 p v <  M13 /\
                               d3 q v0 <= M24 /\
                               condC M13 m12 m14 M24 m34 m23 
                            ==> conv {p , v} INTER conv {q , v0} = {}`);;

let affine_two_points = prove (`!(x:real^3) (y:real^3). affine {z | ?u v. u + v = &1 /\ z = u % x + v % y}`, REPEAT GEN_TAC THEN
                               REWRITE_TAC[affine] THEN REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
                               ASM_REWRITE_TAC[] THEN EXISTS_TAC `( u:real) * u' + v * u''` THEN EXISTS_TAC ` u:real * v' + v * v''` THEN
                               REWRITE_TAC[REAL_RING `(u * u' + v * u'') + u * v' + v * v'' = u * (u' + v') + v * (u'' + v'')`] THEN 
                               ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_RING `u * &1 + v * &1 = u + v`] THEN ASM_REWRITE_TAC[] THEN
                               VECTOR_ARITH_TAC);;

let ch_le = prove (`(!x y u v. x IN t /\ y IN t /\ u + v = &1 ==> u % x + v % y IN t) <=>
                        (!v1 v2 r s. v1 IN t /\ v2 IN t /\ r + s = &1 ==> r % v1 + s % v2 IN t)`, MESON_TAC[]);;

let sub_aff = prove ( ` ! (t:real^3->bool) v1:real^3 v2:real^3 . affine t /\ {v1 , v2} SUBSET t ==> 
                        {w | ?r s. r + s = &1 /\ w = r % v1 + s % v2} SUBSET t`, REPEAT GEN_TAC THEN REWRITE_TAC[affine] THEN
                        REWRITE_TAC[SET_RULE `{v1, v2} SUBSET t <=> v1 IN t /\ v2 IN t`] THEN STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN
                        GEN_TAC THEN ONCE_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
                        UNDISCH_TAC `!x:real^3 y:real^3 u:real v. x IN (t:real^3->bool) /\ y IN t /\ u + v = &1 ==> u % x + v % y IN t` THEN
                        ONCE_REWRITE_TAC[ch_le] THEN UNDISCH_TAC `v1:real^3 IN t:real^3->bool` THEN UNDISCH_TAC `v2:real^3 IN t:real^3->bool` THEN
                        UNDISCH_TAC `r + s = &1 ` THEN MESON_TAC[]);;

let ans = prove (` INTERS {t:real^3->bool | affine t /\ {v1:real^3, v2} SUBSET t} = {w:real^3 | ?r:real s. r + s = &1 /\ w = r % v1 + s % v2}
                     <=> INTERS {t | affine t /\ {v1, v2} SUBSET t} SUBSET {w | ?r s. r + s = &1 /\ w = r % v1 + s % v2} /\
                         {w | ?r s. r + s = &1 /\ w = r % v1 + s % v2} SUBSET INTERS {t | affine t /\ {v1, v2} SUBSET t} `, SET_TAC[]);;

let anss = SET_RULE `(!t:real^3->bool. affine t /\ {v1, v2} SUBSET t ==> {w | ?r s. r + s = &1 /\ w = r % v1 + s % v2} SUBSET t ) ==>
                  {w | ?r s. r + s = &1 /\ w = r % v1 + s % v2} SUBSET INTERS {t | affine t /\ {v1, v2} SUBSET t}`;;

let chon = SET_RULE `!s:A->bool. s IN { t | P t} ==> INTERS { t| P t} SUBSET s`;;

let subset_two_points = SET_RULE `{a , b } SUBSET s <=> a IN s /\ b IN s`;;

let sub_1 = prove (`{w | ?r s. r + s = &1 /\ w = r % (v1:real^3) + s % (v2:real^3)} SUBSET
                      INTERS {(t:real^3->bool) | affine t /\ {v1, v2} SUBSET t}`, MATCH_MP_TAC(anss) THEN REWRITE_TAC[sub_aff]);;

let AFF_HULL_TWO_POINTS = prove (` ! v1:real^3 v2:real^3 . affine hull {v1 , v2} = { w | ? r s . r + s = &1 /\ w = r % v1 + s % v2 }`,
                             REPEAT GEN_TAC THEN REWRITE_TAC[hull] THEN REWRITE_TAC[ans] THEN REWRITE_TAC[sub_1] THEN MATCH_MP_TAC(chon) THEN
                             REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[affine_two_points] THEN REWRITE_TAC[subset_two_points] THEN
                             REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL [EXISTS_TAC `&1`; EXISTS_TAC `&0`] THENL [EXISTS_TAC `&0`; EXISTS_TAC `&1`]
                             THENL [REWRITE_TAC[REAL_ARITH ` &1 + &0 = &1`]; REWRITE_TAC[REAL_ARITH ` &0 + &1 = &1`]] THEN VECTOR_ARITH_TAC);;


(*=========================================================*)

let have_not_proved = new_axiom (`center_pac s v0
 ==> (v IN v_std s v0
      ==> (!p q h.
               {w | {v, w} IN e_std s v0} p /\
               {w | {v, w} IN e_std s v0} q /\
               p = q + h % (v0 - v)
               ==> p = q)) /\
     (v IN v_std s v0
      ==> {w | {v, w} IN e_std s v0} INTER affine hull {v0, v} = {})`);;

g`!(v0:real^3) (s:real^3->bool). center_pac s v0 ==> fan3 (v0,v_std s v0,e_std s v0 )`;;
e(REPEAT GEN_TAC);;
e(REWRITE_TAC[fan3;cyclic_set]);;
e(DISCH_TAC);;
e(GEN_TAC);;
e(REWRITE_TAC[TAUT ` v IN v_std s v0
 ==> ~(v0 = v) /\
     FINITE {w | {v, w} IN e_std s v0} /\
     (!p q h.
          {w | {v, w} IN e_std s v0} p /\
          {w | {v, w} IN e_std s v0} q /\
          p = q + h % (v0 - v)
          ==> p = q) /\
     {w | {v, w} IN e_std s v0} INTER affine hull {v0, v} = {} <=> 
  ( v IN v_std s v0 ==> ~(v0 = v)) /\ ( v IN v_std s v0 ==> FINITE {w | {v, w} IN e_std s v0}) /\
  ( v IN v_std s v0 ==> (!p q h.
          {w | {v, w} IN e_std s v0} p /\
          {w | {v, w} IN e_std s v0} q /\
          p = q + h % (v0 - v)
          ==> p = q)) /\
  ( v IN v_std s v0 ==> {w | {v, w} IN e_std s v0} INTER affine hull {v0, v} = {})`]);;
e(CONJ_TAC);;
e(REWRITE_TAC[v_std;DIFF]);;
e(SET_TAC[]);;
e(CONJ_TAC);;
e(REWRITE_TAC[e_std]);;
e(ONCE_REWRITE_TAC[SET_RULE `{{u, v} | u IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
                      v IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
                      ~(u = v) /\
                      d3 u v <= &2 * t0} = {{x, y} | x IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
                      y IN tru_pack v0 (&2 * t0) s DIFF {v0} /\
                      ~(x = y) /\
                      d3 x y <= &2 * t0}`]);;
e(DISCH_TAC);;
e(ONCE_REWRITE_TAC[lemmaf3]);;
e(MATCH_MP_TAC (lemmaf33));;
e(MATCH_MP_TAC (fini_lemma));;
e(UNDISCH_TAC `center_pac (s:real^3->bool) (v0:real^3)`);;
e(REWRITE_TAC[infi_lemma2]);;
e(UNDISCH_TAC `center_pac (s:real^3->bool) (v0:real^3)`);;
e(REWRITE_TAC[have_not_proved]);;
let fan3_lemma = top_thm();;


(*=====================================================================*)
