 (* Vu Quang Thanh *)

prioritize_num();; 

(* Definition of the tameness, actually I do not need this formally in  my proof      *) 

let triangle = new_definition `triangle (face (H:(A)hypermap) (x:A)) <=> CARD (face H x) = 3`;; 

let quadrilateral = new_definition `quadrilateral (face (H:(A)hypermap) (x:A)) <=> CARD (face H x) = 4`;; 

let exceptional = new_definition `exceptional (face (H:(A)hypermap) (x:A)) <=> CARD (face H x) >= 5`;;

let tr_set = prove (`!(H:(A)hypermap) (x:A). (?tr:A->bool. (!y:A. (node H x) y ==> tr y = triangle (face H y)))`, REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN EXISTS_TAC `triangle (face (H:(A)hypermap) (y:A))` THEN REWRITE_TAC[]);;

let tr_fun = new_specification ["tr_check"] (REWRITE_RULE [SKOLEM_THM] tr_set);;

let set_of_triangle = new_definition `set_of_triangle (H:(A)hypermap) (x:A) = {face H y |y IN node H x /\ tr_check H x y}`;;

let number_of_triangle = new_definition `number_of_triangle (H:(A)hypermap) (x:A) = CARD (set_of_triangle H x)`;;
 
let quad_set = prove (`!(H:(A)hypermap) (x:A). (?qd:A->bool. (!y:A. (node H x) y ==> qd y = quadrilateral (face H y)))`, REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN EXISTS_TAC `quadrilateral (face (H:(A)hypermap) (y:A))` THEN REWRITE_TAC[]);;

let quad_fun = new_specification ["quad_check"] (REWRITE_RULE [SKOLEM_THM] quad_set);;

let set_of_quadrilateral = new_definition `set_of_quadrilateral (H:(A)hypermap) (x:A) = {face H y |y IN node H x /\ quad_check H x y}`;;

let number_of_quadrilateral = new_definition `number_of_quadrilateral (H:(A)hypermap) (x:A) = CARD (set_of_quadrilateral H x)`;;

let ex_set = prove (`!(H:(A)hypermap) (x:A). (?ex:A->bool. (!y:A. (node H x) y ==> ex y = exceptional (face H y)))`, REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN EXISTS_TAC `exceptional (face (H:(A)hypermap) (y:A))` THEN REWRITE_TAC[]);;

let ex_fun = new_specification ["ex_check"] (REWRITE_RULE [SKOLEM_THM] ex_set);;

let set_of_exceptional = new_definition `set_of_exceptional (H:(A)hypermap) (x:A) = {face H y |y IN node H x /\ ex_check H x y}`;;

let number_of_exceptional = new_definition `number_of_exceptional (H:(A)hypermap) (x:A) = CARD (set_of_exceptional H x)`;;

let type_of_node = new_definition `type_of_node (H:(A)hypermap) (x:A) = (number_of_triangle H x, number_of_quadrilateral H x, number_of_exceptional H x)`;;

let tgt = new_definition `tgt = &1541 / &1000`;;

let b_tame  = new_definition `b_tame p q = if p,q = 0,3 then &618 / &1000 else 
                          if p,q = 0,4 then &1 / &1 else
                          if p,q = 1,2 then &66 / &100 else
                          if p,q = 1,3 then &618 / &1000 else
                          if p,q = 2,1 then &8 / &10 else
                          if p,q = 2,2 then &412 / &1000 else
                          if p,q = 2,3 then &12851 / &10000 else
                          if p,q = 3,1 then &315 / &1000 else
                          if p,q = 3,2 then &83 / &100 else
                          if p,q = 4,0 then &35 / &100 else
                          if p,q = 4,1 then &374 / &1000 else
                          if p,q = 5,0 then &4 / &100 else 
                          if p,q = 5,1 then &1144 / &1000 else 
                          if p,q = 6,0 then &689 / &1000 else 
                          if p,q = 7,0 then &145 / &100 else tgt`;;

let d_tame = new_definition `d n = if n = 3 then &0 else 
                      if n = 4 then &206 / &1000 else
                      if n = 5 then &483 / &1000 else 
                      if n = 6 then &760 / &1000 else tgt`;;

let a_tame = new_definition `a_tame = &63 / &100`;;

let weight =
  REWRITE_RULE[]
   (new_type_definition "weight" ("weight","we")
     (prove(`?f:(A->bool)->real. !x. f x >= &0`,EXISTS_TAC `(\x:(A->bool). &0)` THEN REAL_ARITH_TAC)));;

let total_weight = new_definition `total_weight (H:(A)hypermap) (w:(A->bool)->real) = sum (face_set H) w`;;

let adm_1 = new_definition `adm_1 (H:(A)hypermap) (w:(A->bool)->real) <=> (!x:A. w (face H x)  >= d (CARD (face H x)))`;;

let face_of_node = prove (`!(H:(A)hypermap) (x:A). (?fn:A->bool. (!y:A. fn y = ~(node H x INTER face H y = {})))`, REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN EXISTS_TAC `~((node (H:(A)hypermap) (x:A)) INTER (face (H:(A)hypermap) (y:A))= {})` THEN REWRITE_TAC[]);;

let fn_fun = new_specification ["fn_check"] (REWRITE_RULE [SKOLEM_THM] face_of_node);;

let face_set_of_node = new_definition `face_set_of_node (H:(A)hypermap) (x:A) = {face H y |fn_check H x y}`;;

let adm_2 = new_definition `adm_2 (H:(A)hypermap) (w:(A->bool)->real) <=> (!x:A. (number_of_exceptional (H:(A)hypermap) (x:A) = 0) ==> ((sum (face_set_of_node H x) w) >= (b (number_of_triangle H x) (number_of_quadrilateral H x))))`;;

let triangle_of_node = prove (`!(H:(A)hypermap) (x:A). (?trn:A->bool. (!y:A. trn y = (triangle (face H y) /\ ~(node H x INTER face H y = {}))))`, REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN EXISTS_TAC `(triangle (face (H:(A)hypermap) (y:A)) /\ ~((node (H:(A)hypermap) (x:A)) INTER (face (H:(A)hypermap) (y:A))= {}))` THEN REWRITE_TAC[]);;

let trn_fun = new_specification ["trn_check"] (REWRITE_RULE [SKOLEM_THM] triangle_of_node);;

let triangle_set_of_node = new_definition `triangle_set_of_node (H:(A)hypermap) (x:A) = {face H y |trn_check H x y}`;;

let adm_3 = new_definition `adm_3 (H:(A)hypermap) (w:(A->bool)->real) <=> (!x:A. type_of_node H x = 5, 0, 1 ==> (sum (triangle_set_of_node H x) w)  >= a_tame)`;;

let admissible_weight = new_definition `admissible_weight (H:(A)hypermap) (w:(A->bool)->real) <=> adm_1 H w /\ adm_2 H w /\ adm_3 H w`;;

let tame_1 = new_definition `tame_1 (H:(A)hypermap) <=> plain_hypermap (H:(A)hypermap) /\ planar_hypermap (H:(A)hypermap)`;;

let tame_2 = new_definition `tame_2 (H:(A)hypermap) <=> connected_hypermap H /\ simple_hypermap H`;;

let edge_nondegenerate = new_definition `edge_nondegenerate (H:(A)hypermap) (x:A) <=> ~(edge_map H x = x)`;;

let tame_3 = new_definition `tame_3 (H:(A)hypermap)  <=> (!x:A. edge_nondegenerate H x)`;;

let tame_4 = new_definition `tame_4 (H:(A)hypermap)  <=> (!x:A. (!y:A. y IN edge H x /\ ~(y = x) ==> (node H x INTER node H y = {})))`;;

let tame_5 = new_definition `tame_5 (H:(A)hypermap)  <=> (!x:A y:A. ~(y IN node H x) ==> CARD {z:A | ~(edge H z INTER node H x = {}) /\ ~(edge H z INTER node H y = {})} <= 1)`;;


let face_step_contour = new_definition `face_step_contour (H:(A)hypermap) (x:A) (y:A) <=> y = face_map H x`;;

let is_face_contour = new_recursive_definition num_RECURSION  `(is_face_contour (H:(A)hypermap) (p:num->A) 0 <=> T) /\ (is_face_contour (H:(A)hypermap) (p:num->A) (SUC n) <=> ((is_face_contour H p n) /\ face_step_contour H (p n) (p (SUC n))))`;; 

let inj_path = new_recursive_definition num_RECURSION 
   `(inj_path (p:num->A) 0 <=> T) /\ (inj_path (p:num->A) (SUC n) <=> (inj_path p n /\ (!j:num. j <= n ==> ~(p (SUC n) =  p j))))`;;


let is_contour_loop = new_definition `is_contour_loop (H:(A)hypermap) (p:num->A) (n:num) <=> is_contour H p n /\ inj_path p (n - 1) /\ p n = p 0`;;

let is_face_loop = new_definition `is_face_loop (H:(A)hypermap) (p:num->A) (n:num) <=> is_face_contour H p n /\ inj_path p (n - 1) /\ p n = p 0`;; 
 
let one_step = new_definition `one_step (H:(A)hypermap) (x:A) (y:A) <=> go_one_step H x y \/ go_one_step H y x`;; 

let interior_contour = new_definition `interior_contour (H:(A)hypermap) (p:num->A) (n:num) (y:A) <=> is_contour_loop H p n /\ (?(m:num) (q:num->A). q m = y /\ q 0 = p 0 /\ is_contour H q m)`;; 

let set_of_interior_contour = new_definition `set_of_interior_contour (H:(A)hypermap) (p:num->A) (n:num) = {y:A | interior_contour H p n y}`;; 

let node_interior_contour = new_definition `node_interior_contour (H:(A)hypermap) (p:num->A) (n:num) (y:A) <=> !z:A. z IN node H y ==> interior_contour H p n z`;; 

let exterior_contour = new_definition `exterior_contour (H:(A)hypermap) (p:num->A) (n:num) (y:A) <=> (is_contour_loop H p n /\ ~(interior_contour H p n y))`;; 

let set_of_exterior_contour = new_definition `set_of_exterior_contour (H:(A)hypermap) (p:num->A) (n:num) = {y:A | exterior_contour H p n y}`;; 

let node_exterior_contour = new_definition `node_exterior_contour (H:(A)hypermap) (p:num->A) (n:num) (y:A) <=> !z:A. z IN node H y ==> exterior_contour H p n z`;; 

let tame_6 = new_definition `tame_6 (H:(A)hypermap)  <=> (!p:num->A. (is_face_loop H p 3 /\ (?y:A. node_exterior_contour H p 3 y)) ==> (?x:A. face H x = {p 0, p 1, p 2}))`;;

let tame_7 = new_definition `tame_7 (H:(A)hypermap)  <=> (!p:num->A. (is_contour_loop H p 4 /\ (?y:A z:A. node_exterior_contour H p 4 y /\ node_exterior_contour H p 4 z)) ==> (set_of_interior_contour H p 4 = {p 0, p 1, p 2, p 3} /\ (one_step H (p 0) (p 2) \/ one_step H (p 1) (p 3) \/ (one_step H (p 0) (p 2) /\ one_step H (p 1) (p 3)))))`;;

let tame_8 = new_definition `tame_8 (H:(A)hypermap)  <=> number_of_faces H >= 3`;;

let tame_9 = new_definition `tame_9 (H:(A)hypermap)  <=> (!(x:A). CARD (face H x) >= 3 /\ CARD (face H x) <= 6)`;;

let tame_10 = new_definition `tame_10 (H:(A)hypermap) <=> number_of_nodes H = 13 \/ number_of_nodes H = 14`;;

let tame_11 = new_definition `tame_11 (H:(A)hypermap) <=> (!(x:A). CARD (node H x) >= 3 /\ CARD (node H x) <= 7)`;;

let tame_12 = new_definition `tame_12 (H:(A)hypermap) <=> (!(x:A) (y:A). (~((node H x) INTER (face H y) = {}) /\ exceptional (face H y)) ==> (CARD (node H x) <= 6 /\ CARD (node H x) = 6 ==> type_of_node H x = 5,0,1))`;; 

let tame_13 = new_definition `tame_13 (H:(A)hypermap) <=> (?(w:(A->bool)->real). admissible_weight H w /\ total_weight H w <= tgt)`;;

let tame_hypermap = define `tame_hypermap (H:(A)hypermap) <=> tame_1 H /\ tame_2 H /\ tame_3 H /\ tame_4 H /\ tame_5 H /\ tame_6 H /\ tame_7 H /\ tame_8 H /\ tame_9 H /\ tame_10 H /\ tame_11 H /\ tame_12 H /\ tame_13 H` ;;


(* Definition of the opposite hypermap and some lemmas concerned. *)

let opposite = new_definition `opposite (H:(A)hypermap) = hypermap (FST (tuple_hypermap H), SND (SND (SND (tuple_hypermap H))) o FST (SND (SND (tuple_hypermap H))), inverse (FST (SND (SND (tuple_hypermap H)))), inverse (SND (SND (SND (tuple_hypermap H)))))`;;



let permutes_ID_ab = prove (`!D:A->bool e:A->A n:A->A. FINITE D /\ e permutes D /\ n permutes D ==> (e o n = I <=> n o e = I)`, let lm1 = prove (`!D:A->bool e:A->A n:A->A. FINITE D /\ e permutes D /\ n permutes D ==> e o n = I ==> n o e = I`, REPEAT STRIP_TAC THEN MP_TAC (ISPECL[`e:A->A`;`D:A->bool`] PERMUTES_INVERSES_o) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL[`inverse (e:A->A)`; `(e:A->A) o (n:A->A)`; `I:A->A`] LEFT_MULT_MAP) THEN ASM_REWRITE_TAC[o_ASSOC] THEN REWRITE_TAC[I_O_ID] THEN DISCH_TAC THEN ASM_REWRITE_TAC[]) in MESON_TAC[lm1]);;

let plain_op_lm = prove (`!D:A->bool e:A->A n:A->A f:A->A. FINITE D /\ e permutes D /\ n permutes D /\  f permutes D /\ e o n o f = I /\ e o e = I ==> f o n o f o n = I`, REPEAT STRIP_TAC THEN MP_TAC (ISPECL[`e:A->A`;`D:A->bool`] PERMUTES_INVERSES_o) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL[`inverse (e:A->A)`; `(e:A->A) o (n:A->A) o (f:A->A)`; `(e:A->A) o (e:A->A)`] LEFT_MULT_MAP) THEN ASM_REWRITE_TAC[o_ASSOC;I_O_ID] THEN DISCH_TAC THEN MP_TAC(MESON [GSYM o_ASSOC] `(n:A->A) o (f:A->A) = e ==> (f o n) o f = f o e`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL[`D:A->bool`; `e:A->A`; `n:A->A`; `f:A->A`] cyclic_maps) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_SIMP_TAC[GSYM o_ASSOC]);;


prioritize_real();;

(* Definition of fan, and the construction of the hypermap of fan. I follow the things on the sphere.hl and fan.ml, actually, I modify to fit the part on hypermap  *)

let atn2 = new_definition (`atn2 (x,y) =
    if ( abs y < x ) then atn(y / x) else
    (if (&0 < y) then ((pi / &2) - atn(x / y)) else
    (if (y < &0) then (-- (pi/ &2) - atn (x / y)) else (  pi )))`);;

let aff = new_definition `aff = ( hull ) affine`;;
let radius = new_definition `radius (x,y) = sqrt((x pow 2) + (y pow 2))`;;
let polar_angle = new_definition `polar_angle x y = 
         let theta = atn2(x,y) in
	 if (theta < &0) then (theta + (&2 * pi)) else theta`;;
let polar_c = new_definition `polar_c x y = (radius (x,y),polar_angle x y)`;;

let directed_angle = new_definition `directed_angle (x,y) (x',y') = 
  polar_angle (x'*x+y'*y) (y'*x - x'*y)`;;
let polar_cycle = new_definition `polar_cycle V v = (@ u. V u /\
  (!w. V w /\ ~(w = v)  ==> directed_angle v u <= directed_angle v w))`;;

let orthonormal = new_definition `orthonormal e1 e2 e3 = 
     (( e1 dot e1 = &1) /\ (e2 dot e2 = &1) /\ ( e3 dot e3 = &1) /\
     ( e1 dot e2 = &0) /\ ( e1 dot e3 = &0) /\ ( e2 dot e3 = &0) /\
     (&0 <  (e1 cross e2) dot e3))`;;

let cyclic_set = new_definition `cyclic_set W v w = 
     (~(v=w) /\ (FINITE W) /\ (!p q h. W p /\ W q /\ (p = q + h % (v - w)) ==> (p=q)) /\
        (W INTER (affine hull {v,w}) = EMPTY))`;;

let azim_cycle_hyp_def = new_definition `azim_cycle_hyp = 
  (?sigma.  !W proj v w e1 e2 e3 p. 
        (W p) /\
        (cyclic_set W v w) /\ ((dist( v ,w)) % e3 = (w-v)) /\
	(orthonormal e1 e2 e3) /\ 
	(!u x y. (proj u = (x,y)) <=> (?h. (u = v + x % e1 + y % e2 + h % e3))) ==>
	(proj (sigma W v w p) = polar_cycle (IMAGE proj W) (proj p)))`;;

let azim_cycle_spec = prove(`?sigma. !W proj v w e1 e2 e3 p.
   (azim_cycle_hyp) ==> ( (W p) /\
        (cyclic_set W v w) /\ ((dist( v ,w)) % e3 = (w-v)) /\
	(orthonormal e1 e2 e3) /\ 
	(!u x y. (proj u = (x,y)) <=> (?h. (u = v + x % e1 + y % e2 + h % e3)))) ==> (proj (sigma W v w p) = polar_cycle (IMAGE proj W) (proj p))`,
	(REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM;GSYM RIGHT_IMP_FORALL_THM]) THEN
	  (REWRITE_TAC[azim_cycle_hyp_def])
	   );;

let azim_cycle_def = new_specification ["azim_cycle"] azim_cycle_spec;;	

let graph = new_definition `graph (E:(A->bool)->bool) <=> (!e. E e ==> e HAS_SIZE 2)`;;

let fan1 = new_definition `fan1 (V:A->bool) <=> FINITE V /\ ~(V = {})`;;

let fan2 = new_definition `fan2 (x:A, V) <=> ~(x IN V)`;;

let fan3 = new_definition `fan3 (x:real^3,V,E) <=> (!v. v IN V ==> cyclic_set {w | {v,w} IN E } x v)`;;

let fan4 = new_definition `fan4 (x:real^3,V,E) <=> (!e. (e IN E) ==> (aff_gt {x} e  INTER V={}))`;;

let fan5 = new_definition `fan5 (x:real^3,E) <=> (!e f. (e IN E)/\ (f IN E) /\ ~(e = f) ==> (aff_gt {x} e INTER aff_gt {x} f ={}))`;;

let fan = new_definition `fan (x:real^3, V, E) <=> ((UNIONS E) SUBSET V) /\ graph E/\ fan1 V /\ fan2 (x,V)/\ fan3 (x,V,E)/\ fan4 (x,V,E) /\ fan5 (x,E)`;;

let base_point_fan = new_definition `base_point_fan (x:A,V:A->bool,E:(A->bool)->bool) = x`;;

let incident_edges = new_definition `incident_edges (v:A) E = {w | {v,w} IN E}`;;

let azim_cycle_fan = new_definition `azim_cycle_fan  = 
(!x:real^3 V E. ?sigma. !proj e1 e2 e3 v w. 
(fan(x, V, E) /\ (V v) /\ ({v,w} IN E) /\ ((dist(v,x)) % e3 = (x-v)) /\
(orthonormal e1 e2 e3) /\ (!u a b. (proj u = (a,b)) <=> (?h. (u = v + a % e1 + b % e2 + h % e3)))) ==> (  (proj (sigma  v w) = polar_cycle (IMAGE proj {y|{v,y} IN E}) (proj w))))`;;

let azim_cycle_fan1 = REWRITE_RULE[SKOLEM_THM] azim_cycle_fan;;

let azim_cycle_fan2 = prove(`?sigma. !x:real^3 V E proj e1 e2 e3 v w. 
(azim_cycle_fan)==> (fan(x, V, E) /\ (V v) /\ ({v,w} IN E) /\ ((dist(v,x)) % e3 = (x-v)) /\ (orthonormal e1 e2 e3) /\ (!u a b. (proj u = (a,b)) <=> (?h. (u = v + a % e1 + b % e2 + h % e3)))) ==> (  (proj (sigma x V E v w) = polar_cycle (IMAGE proj {y|{v,y} IN E}) (proj w)))`, REWRITE_TAC[GSYM RIGHT_IMP_FORALL_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN REWRITE_TAC[azim_cycle_fan1]);;
	

let sigma_fan = new_specification ["sigma_fan"] azim_cycle_fan2;;

let D1 = new_definition `D1 (x:real^3,V:real^3->bool,E:(real^3->bool)->bool) = {(x:real^3,v:real^3,w:real^3,w1:real^3)|(V v)/\(w IN incident_edges v E) /\ (w1 = sigma_fan x V E v w)}`;;

let D2 = new_definition `D2 (x:real^3,V:real^3->bool,E:(real^3->bool)->bool) = {(x,v,v,v)| (V v) /\ (incident_edges v E = {})}`;;

let dart_fan = new_definition `dart_fan (x, V, E) = D1 (x, V, E) UNION D2 (x, V, E)`;;

let inverse_sigma_fan = new_definition `inverse_sigma_fan x V E v w = @a. sigma_fan x V E v a=w`;;

let e_fan = new_definition `e_fan (x:real^3) V E = (\((x:real^3),(v:real^3),(w:real^3),(w1:real^3)). (x,w,v,(sigma_fan x V E w v)))`;;

let f_fan = new_definition `f_fan (x:real^3) V E = (\((x:real^3),(v:real^3),(w:real^3),(w1:real^3)). (x,w,(inverse_sigma_fan x V E w v),v) )`;;

let n_fan = new_definition `n_fan (x:real^3) V E = (\(x:real^3,v:real^3,w:real^3,w1:real^3). (x, v, w1, sigma_fan x V E v w1))`;;

let azim_dart = new_definition `azim_dart (x, v, w, w1) = azim x v w w1`;;

let hypermap_of_fan = new_definition `hypermap_of_fan (x:real^3, V, E) = hypermap (dart_fan (x, V, E), e_fan x V E, n_fan x V E, f_fan x V E)`;;

(* I made the following as my assumption, this should have been done in the fan part, by that I means, actually when you need a hypermap out of a fan *)

let hyp_fan1 = prove (`!x:real^3 V E. fan (x, V, E) ==> FINITE (dart_fan (x, V, E))`, CHEAT_TAC);;

let hyp_fan2 = prove (`!x:real^3 V E. fan (x, V, E) ==> (e_fan x V E) permutes dart_fan (x, V, E)`, CHEAT_TAC);;

let hyp_fan3 = prove (`!x:real^3 V E. fan (x, V, E) ==> (n_fan x V E) permutes dart_fan (x, V, E)`, CHEAT_TAC);;

let hyp_fan4 = prove (`!x:real^3 V E. fan (x, V, E) ==> (f_fan x V E) permutes dart_fan (x, V, E)`, CHEAT_TAC);;

let hyp_fan5 = prove (`!x:real^3 V E. fan (x, V, E) ==> (e_fan x V E) o (n_fan x V E) o (f_fan x V E) = I`, CHEAT_TAC);;

(* If the above assumption, the followings are the properties of the hypermap associated with the fan *)

let hyp_fan_tup = prove (`!x:real^3 V E. fan (x, V, E) ==> tuple_hypermap (hypermap (dart_fan (x,V,E), e_fan x V E, n_fan x V E, f_fan x V E)) = (dart_fan (x,V,E), e_fan x V E, n_fan x V E, f_fan x V E)`, SIMP_TAC[GSYM (CONJUNCT2 hypermap_tybij); hyp_fan1;hyp_fan2;hyp_fan3;hyp_fan4;hyp_fan5;SND;FST]);;

let n_hyp_of_fan = prove (`!x:real^3 V E. fan (x, V, E) ==> node_map (hypermap_of_fan (x, V, E)) = n_fan x V E`, SIMP_TAC[hyp_fan_tup;node_map;FST;SND;hypermap_of_fan]);;

let e_hyp_of_fan = prove (`!x:real^3 V E. fan (x, V, E) ==> edge_map (hypermap_of_fan (x, V, E)) = e_fan x V E`, SIMP_TAC[hyp_fan_tup;edge_map;FST;SND;hypermap_of_fan]);;

let f_hyp_of_fan = prove (`!x:real^3 V E. fan (x, V, E) ==> face_map (hypermap_of_fan (x, V, E)) = f_fan x V E`, SIMP_TAC[hyp_fan_tup;face_map;FST;SND;hypermap_of_fan]);;

(* A lemma on the bound of the sum related to the cardinality *)

let card_node = new_definition `card_node x V E n = CARD (node (hypermap_of_fan (x, V, E)) n)`;;

let SUM_LOWER_BOUND = prove (`!s f a. FINITE s /\ (!x:A. x IN s ==> a <= f (x)) ==> &(CARD s) * a <= sum s f`, SIMP_TAC[GSYM SUM_CONST; SUM_LE]);;

let node_lbound_lm = prove (`!a (x:real^3) V E n. fan (x, V, E) /\ (!d. a <= azim_dart d) /\ FINITE (node (hypermap_of_fan (x, V, E)) n) ==> &(card_node x  V E n) * a <= sum (node (hypermap_of_fan (x, V, E)) n) azim_dart`, SIMP_TAC [SUM_LOWER_BOUND;card_node]);; 

(* Characterization of the node in hypermap associated with a fan *)

let pow_sigma_fan = new_recursive_definition num_RECURSION  `(pow_sigma_fan (x:real^3) V E v w 0 = w) /\ (pow_sigma_fan (x:real^3) V E v w (SUC n) = (sigma_fan x V E v (pow_sigma_fan x V E v w n)))`;; 

let pow_sigma_0 = prove (`!x V E v w. pow_sigma_fan x V E v w 0 = w`, SIMP_TAC[pow_sigma_fan]);;

let pow_sigma_1 = prove (`!x V E v w. pow_sigma_fan x V E v w 1 = sigma_fan x V E v w`, SIMP_TAC[pow_sigma_fan;pow_sigma_0;ARITH_RULE `1 = SUC 0`]);;


let node_fan_map = prove (`!x V E v w i. fan (x, V, E) ==> node_map (hypermap_of_fan (x, V, E)) (x, v, pow_sigma_fan x V E v w i, pow_sigma_fan x V E v w (SUC i)) = (x, v, pow_sigma_fan x V E v w (SUC i), pow_sigma_fan x V E v w (SUC (SUC i)))`, REPEAT STRIP_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`] n_hyp_of_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[n_fan;pow_sigma_fan]);;

let in_d1 = prove (`!x V E v w w1. (x, v, w, w1) IN D1 (x, V, E) ==> w1 = sigma_fan x V E v w`, REWRITE_TAC[D1;IN_ELIM_THM;PAIR_EQ] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* The following is also not necessary in my task, I put it for the coherent, and following the note, actually, we need to redefine the node edge, face map in the hypermap associated with a fan, and it should be modified in the fan part *) 

let dart_fan_character = prove (`!x V E v w w1. (x, v, w, w1) IN dart_fan (x, V, E) <=> w1 = sigma_fan x V E v w`, CHEAT_TAC);;


let MULT_INVERSE_POWER = prove (`!D:A->bool e:A->A. FINITE D /\ e permutes D ==> (!n. (e POWER n) o ((inverse e) POWER n) = I)`, REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC (ISPECL[`e:A->A`;`D:A->bool`] PERMUTES_INVERSES_o) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN INDUCT_TAC THENL[ASM_REWRITE_TAC[POWER;I_O_ID]; MP_TAC (ISPECL[`e:A->A`; `D:A->bool`] PERMUTES_INVERSE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ABBREV_TAC `f = inverse (e:A->A)` THEN MP_TAC (ISPECL [`n:num`; `f:A->A`] COM_POWER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[o_ASSOC] THEN ASM_REWRITE_TAC[POWER;I_O_ID] THEN ASSUME_TAC (ISPECL [`(e:A->A) POWER n`; `e:A->A`; `f:A->A`] (GSYM o_ASSOC)) THEN ASM_SIMP_TAC[I_O_ID]]);;

let pow_node_fan = prove (`!x V E v w. fan (x, V, E) ==> (!i. (node_map (hypermap_of_fan (x, V, E)) POWER i) (x, v, w, sigma_fan x V E v w) = (x, v, pow_sigma_fan x V E v w i, pow_sigma_fan x V E v w (SUC i)))`, REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL[REWRITE_TAC[POWER;I_THM;pow_sigma_0;pow_sigma_1; ARITH_RULE `SUC 0 = 1`]; ASM_REWRITE_TAC[COM_POWER;o_THM] THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`; `v:real^3`;`w:real^3`; `i:num`] node_fan_map) THEN ASM_REWRITE_TAC[]]);;


let in_orb = prove (`!f:A->A x:A y:A. y IN orbit_map f x <=> (?n. y = (f POWER n) x)`, let lm1 = prove (`!f:A->A x:A y:A. y IN orbit_map f x ==> (?n. y = (f POWER n) x)`, REWRITE_TAC[orbit_map; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]) in let lm2 = prove (`!f:A->A x:A y:A. (?n. y = (f POWER n) x) ==> y IN orbit_map f x`, REPEAT STRIP_TAC THEN MP_TAC (SPECL [`f:A->A`;`n:num`;`x:A`;`y:A`] in_orbit_lemma) THEN ASM_REWRITE_TAC[]) in MESON_TAC[lm1;lm2]);;



let INV_MULT_POW = prove (`!D:A->bool e:A->A. FINITE D /\ e permutes D ==> (!n. ((inverse e) POWER n) o (e POWER n) = I)`, let INV_INVERSE = prove (`!s:A->bool p. p permutes s ==> inverse(inverse p) = p`, SIMP_TAC[FUN_EQ_THM] THEN MESON_TAC[PERMUTES_INVERSE_EQ; PERMUTES_INVERSE]) in REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC (ISPECL[`D:A->bool`; `e:A->A`] INV_INVERSE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`e:A->A`;`D:A->bool`] PERMUTES_INVERSE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`D:A->bool`; `inverse (e:A->A)`] MULT_INVERSE_POWER) THEN ASM_SIMP_TAC[]);;

let triv_ch = prove (`!a:num->A n. {a i | i >= 0 /\ i < n} = {a i | i < n}`, REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN STRIP_TAC THEN EQ_TAC THENL[REPEAT STRIP_TAC THEN EXISTS_TAC `i:num` THEN ASM_SIMP_TAC[]; REPEAT STRIP_TAC THEN EXISTS_TAC `i:num` THEN ASM_SIMP_TAC[] THEN ARITH_TAC]);;

let lm1 = prove (`!s:A->bool p:A->A m n. FINITE s /\ p permutes s ==> (inverse p POWER n) o (p POWER (n + m)) = p POWER m`, REPEAT STRIP_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`] INV_MULT_POW) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (ASSUME_TAC o SPEC `n:num`) THEN ASSUME_TAC (MESON [addition_exponents] `(p:A->A) POWER (n + m) = (p POWER n) o (p POWER m)`) THEN ASM_REWRITE_TAC[o_ASSOC; I_O_ID]);;
  
let lm2 = prove (`!s:A->bool p:A->A (n:num) x:A. FINITE s /\ p permutes s ==> ((!m:num. ~(m = 0) /\ (m < n) ==> ~((p POWER m) x = x)) ==> (!i:num j:num. (i < n) /\ (j < i) ==> ~((p POWER i) x = (p POWER j) x)))`, REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_THEN (LABEL_TAC "c3") THEN REPLICATE_TAC 3 STRIP_TAC THEN DISCH_THEN (LABEL_TAC "c4") THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP LM_AUX) THEN REPEAT STRIP_TAC THEN REMOVE_THEN "c3" MP_TAC THEN MP_TAC (ARITH_RULE `(i:num < n:num) /\ (i = (j:num) + (k:num)) ==> k < n`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_THEN (MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`; `k:num`; `j:num`] lm1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`] INV_MULT_POW) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (ASSUME_TAC o SPEC `j:num`) THEN MP_TAC (MESON [o_THM] `((p:A->A) POWER i) x = (p POWER j) x ==> ((inverse p POWER j) o (p POWER i)) x = ((inverse p POWER j) o (p POWER j)) x`) THEN ASM_REWRITE_TAC[I_O_ID; I_THM]);;
 
let lm3 = prove (`!s:A->bool p:A->A x:A. FINITE s /\ p permutes s ==> (!m:num. ~(m = 0) /\ (m < CARD (orbit_map p x)) ==> ~((p POWER m) x = x))`, REPEAT STRIP_TAC THEN MP_TAC (ISPECL[`p:A->A`; `m:num`; `x:A`] card_orbit_le) THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;
  
let lm4 = prove (`!s:A->bool p:A->A x:A m n. FINITE s /\ p permutes s ==> ((p POWER (m +n)) x = (p POWER m) x ==> (p POWER n) x = x)`, REPEAT STRIP_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`; `n:num`; `m:num`] lm1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`] INV_MULT_POW) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (ASSUME_TAC o SPEC `m:num`) THEN MP_TAC (MESON [o_THM] `((p:A->A) POWER (m + n)) x = (p POWER m) x ==> ((inverse p POWER m) o (p POWER (m + n))) x = ((inverse p POWER m) o (p POWER m)) x`) THEN ASM_REWRITE_TAC[I_O_ID; I_THM]);; 

let lm5 = prove (`!s:A->bool p:A->A x:A. FINITE s /\ p permutes s ==> (!i:num j:num. (i < CARD (orbit_map (p:A->A) x)) /\ (j < i) ==> ~((p POWER i) x = (p POWER j) x))`, REPLICATE_TAC 7 STRIP_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`; `x:A`] lm3) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`; `CARD (orbit_map (p:A->A) x)`; `x:A`] lm2) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `i:num`) THEN DISCH_THEN (MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[]);;
 
let fin_lem = prove (`!s:A->bool p:A->A x. FINITE s /\ p permutes s ==> FINITE (orbit_map p x)`, REPEAT STRIP_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`] finite_order) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (X_CHOOSE_TAC `n:num`) THEN SUBGOAL_THEN `((p:A->A) POWER n) x = x` ASSUME_TAC THENL[ASM_SIMP_TAC[I_THM]; MP_TAC (ISPECL [`p:A->A`; `n:num`; `x:A`] orbit_cyclic) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL[`n:num`; `(\i. ((p:A->A) POWER i) x)`] FINITE_SERIES) THEN REWRITE_TAC[BETA_CONV `(\i. ((p:A->A) POWER i) x) i`] THEN ASM_SIMP_TAC[]]);; 

let abcd = prove (`!s:A->bool p:A->A x n. {(p POWER i) x | i >= 0 /\ i < n} SUBSET orbit_map p x`, REPEAT STRIP_TAC THEN REWRITE_TAC[orbit_map] THEN SET_TAC[]);; 

let lm_sub_inc = prove (`!s:A->bool p:A->A x n. {(p POWER i) x | i >= 0 /\ i < n} SUBSET {(p POWER i) x | i >= 0 /\ i < SUC n}`, REPEAT STRIP_TAC THEN REWRITE_TAC[orbit_map; SUBSET] THEN GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC [] THEN ASM_ARITH_TAC);;
 
let lm6 = prove (`!p:A->A x n. FINITE {(p POWER i) x | i >= 0 /\ i < n}`, REPEAT STRIP_TAC THEN MP_TAC (ISPECL [`n:num`; `(\i. ((p:A->A) POWER i) x)`] FINITE_SERIES) THEN BETA_TAC THEN MP_TAC (ISPECL [`\i. ((p:A->A) POWER i) x`; `n:num`] triv_ch) THEN BETA_TAC THEN SIMP_TAC[]);;
 
let lm7 = prove (`!s:A->bool p:A->A x n. FINITE s /\ p permutes s ==> CARD {(p POWER i) x | i >= 0 /\ i < n} <= CARD (orbit_map p x) /\ CARD {(p POWER i) x | i >= 0 /\ i < n} <= CARD {(p POWER i) x | i >= 0 /\ i < SUC n}`, REPEAT STRIP_TAC THENL [MP_TAC (ISPECL [`s:A->bool`; `p:A->A`; `x:A`] fin_lem) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`; `x:A`; `n:num`] abcd) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`{((p:A->A) POWER i) x | i >= 0 /\ i < n}`; `orbit_map (p:A->A) x`] NEW_CARD_SUBSET) THEN ASM_REWRITE_TAC[]; MP_TAC (ISPECL [`p:A->A`; `x:A`; `SUC n`] lm6) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`; `x:A`; `n:num`] lm_sub_inc) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`{((p:A->A) POWER i) x | i >= 0 /\ i < n}`; `{((p:A->A) POWER i) x | i >= 0 /\ i < SUC n}`] NEW_CARD_SUBSET) THEN ASM_REWRITE_TAC[]]);;
 
let lm9 = prove (`!s:A->bool p:A->A x. FINITE s /\ p permutes s ==> (!n. CARD (orbit_map (p:A->A) x) <= n ==> CARD {(p POWER i) x |i >= 0 /\ i < n} = CARD (orbit_map (p:A->A) x))`, let NULL_SERIES_1 = prove(`!f:num->A. {f(i) | i >= 0 /\ i < 0} = {}`, GEN_TAC THEN REWRITE_TAC[EXTENSION; EMPTY; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN FIRST_ASSUM (MP_TAC o MATCH_MP (ARITH_RULE `i < 0 ==> F`)) THEN SIMP_TAC[]) in REPLICATE_TAC 4 STRIP_TAC THEN INDUCT_TAC THENL [REWRITE_TAC[ARITH_RULE `i <= 0 <=> i = 0`] THEN DISCH_TAC THEN MP_TAC (ISPEC `\i. ((p:A->A) POWER i) x` NULL_SERIES_1) THEN BETA_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[CARD_CLAUSES]; DISCH_TAC THEN ASM_CASES_TAC `CARD (orbit_map (p:A->A) x) <= n` THENL [SUBGOAL_THEN `CARD {((p:A->A) POWER i) x | i >= 0 /\ i < n} = CARD (orbit_map (p:A->A) x)` ASSUME_TAC THENL [ASM_MESON_TAC[]; MP_TAC (ISPECL [`s:A->bool`; `p:A->A`; `x:A`; `n:num`] lm7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`; `x:A`; `SUC n`] lm7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_ARITH_TAC]; MP_TAC (ARITH_RULE `CARD (orbit_map (p:A->A) x) <= SUC n /\ ~(CARD (orbit_map (p:A->A) x) <= n) ==> CARD (orbit_map (p:A->A) x) = SUC n`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`SUC n`; `\i:num. ((p:A->A) POWER i) x`] CARD_FINITE_SERIES_EQ) THEN BETA_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`; `x:A`] lm5) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN SUBGOAL_THEN `{((p:A->A) POWER i) x | i < SUC n} = {((p:A->A) POWER i) x | i >= 0 /\ i < SUC n}` ASSUME_TAC THENL[REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN SIMP_TAC [ARITH_RULE `i >= 0`]; ASM_MESON_TAC[]]]]);;
 
let orbit_character = prove (`!s:A->bool p:A->A x. FINITE s /\ p permutes s ==> (!n. CARD (orbit_map (p:A->A) x) <= n ==> {(p POWER i) x |i >= 0 /\ i < n} = orbit_map (p:A->A) x)`, REPEAT STRIP_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`; `x:A`] fin_lem) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`; `x:A`; `n:num`] abcd) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`s:A->bool`; `p:A->A`; `x:A`] lm9) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`{((p:A->A) POWER i) x | i >= 0 /\ i < n}`; `orbit_map (p:A->A) x`] CARD_SUBSET_EQ) THEN ASM_REWRITE_TAC[]);;


let node_fan_character = prove (`!x V E v w w1. fan (x, V, E) /\ (x, v, w, w1) IN D1 (x, V, E) ==> (!n. card_node x V E (x, v, w, w1) <= n ==> node (hypermap_of_fan (x, V, E)) (x, v, w, w1) =  {(x, v, pow_sigma_fan x V E v w i, pow_sigma_fan x V E v w (SUC i)) | i >= 0 /\ i < n})`, REPEAT STRIP_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`; `v:real^3`; `w:real^3`; `w1:real^3`] in_d1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[node] THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`] hyp_fan1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`] hyp_fan3) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`] n_hyp_of_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`dart_fan (x:real^3, V, E)`; `n_fan (x:real^3) V E`; `((x:real^3), (v:real^3), (w:real^3), sigma_fan (x:real^3) V E (v:real^3) (w:real^3))`] orbit_character) THEN ASM_REWRITE_TAC[] THEN ABBREV_TAC `m = CARD (orbit_map (n_fan (x:real^3) V E) (x:real^3,v:real^3,w:real^3,sigma_fan (x:real^3) V E v w))` THEN SUBGOAL_THEN `(m:num) <= (n:num)` ASSUME_TAC THENL[ASM_MESON_TAC[card_node;node]; DISCH_THEN (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`; `v:real^3`; `w:real^3`] pow_node_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_SIMP_TAC[]]);;

 
let card_orb_neq0 = prove (`!s:A->bool p:A->A x:A. FINITE s /\ p permutes s ==> ~(CARD (orbit_map p x) = 0)`, REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC (ISPECL[`s:A->bool`; `p:A->A`; `x:A`] fin_lem) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASSUME_TAC (ISPECL [`p:A->A`; `x:A`] orbit_reflect) THEN MP_TAC (ISPECL [`orbit_map (p:A->A) x`; `x:A`] CARD_ATLEAST_1) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;


let card_nfan_neq0 = prove (`!x V E v w w1. fan (x, V, E) /\ (x, v, w, w1) IN D1 (x, V, E) ==> ~(CARD (orbit_map (n_fan x V E) (x, v, w, w1)) = 0)`, REPEAT GEN_TAC THEN STRIP_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`; `v:real^3`; `w:real^3`; `w1:real^3`] in_d1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`] hyp_fan1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`] hyp_fan3) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`dart_fan (x:real^3, V:real^3->bool, E:(real^3->bool)->bool)`; `n_fan (x:real^3) V E`; `(x:real^3, v:real^3, w:real^3, w1:real^3)`] card_orb_neq0) THEN ASM_REWRITE_TAC[]);;


(* Characterization of the sum in a node, related to the sum in a segment, that is a communication with the things on part 1, related to azim *)

let sum_in_seg = prove (`!f:A->real s:A->bool n a:num->A. ~(n = 0) /\ s = {a i | i >= 0 /\ i < n} /\ (!i j. i < j /\ j < n ==> ~(a i = a j)) ==> sum s f = sum (0..(n - 1)) (f o a)`, REPEAT GEN_TAC THEN DISCH_THEN (CONJUNCTS_THEN2 (ASSUME_TAC) (CONJUNCTS_THEN2 (ASSUME_TAC) (LABEL_TAC "h1"))) THEN SUBGOAL_THEN `!i j. i IN 0..n - 1 /\ j IN 0..n - 1 /\ (a:num->A) i = a j ==> i = j` ASSUME_TAC THENL[REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN MP_TAC (ARITH_RULE `i <= n - 1 /\ j <= n - 1 /\ ~(n = 0) ==> i < n /\ j < n`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_CASES_TAC `(i:num) < j` THENL[USE_THEN "h1" (fun th -> MP_TAC (SPECL [`i:num`; `j:num`] th)) THEN ASM_MESON_TAC[]; ASM_CASES_TAC `(j:num) < i` THENL[USE_THEN "h1" (fun th -> MP_TAC (SPECL [`j:num`; `i:num`] th)) THEN ASM_MESON_TAC[]; ASM_ARITH_TAC]]; MP_TAC (ISPECL [`n:num`; `a:num->A`] IMAGE_SEG) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASSUME_TAC (ISPECL [`a:num->A`; `n:num`] triv_ch) THEN MP_TAC (ISPECL [`a:num->A`; `f:A->real`; `0..n - 1`] SUM_IMAGE) THEN ASM_REWRITE_TAC[]]);;

let alt_azim_fan_sum = prove (`!x V E v w w1. fan (x, V, E) /\ (x, v, w, w1) IN D1 (x, V, E) ==> sum (node (hypermap_of_fan (x, V, E)) (x, v, w, w1)) azim_dart = sum (0..((card_node x V E (x, v, w, w1)) - 1)) (\i. azim x v (pow_sigma_fan x V E v w i) (pow_sigma_fan x V E v w (SUC i)))`, REPEAT STRIP_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`; `v:real^3`; `w:real^3`; `w1:real^3`] in_d1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`; `v:real^3`; `w:real^3`; `w1:real^3`] node_fan_character) THEN ASM_REWRITE_TAC[] THEN ABBREV_TAC `m = CARD (orbit_map (n_fan (x:real^3) V E) (x:real^3,v:real^3,w:real^3,sigma_fan (x:real^3) V E v w))` THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`] n_hyp_of_fan) THEN ASM_REWRITE_TAC[card_node;node] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`; `v:real^3`; `w:real^3`; `w1:real^3`] card_nfan_neq0) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`] hyp_fan1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`] hyp_fan3) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`dart_fan (x:real^3, V:real^3->bool, E:(real^3->bool)->bool)`; `n_fan (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool)`; `(x:real^3, v:real^3, w:real^3, w1:real^3)`] lm5) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`; `v:real^3`; `w:real^3`] pow_node_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`azim_dart`; `{(x , v , pow_sigma_fan x V E v w i, pow_sigma_fan x V E v w (SUC i)) | i >= 0 /\ i < m}`; `m:num`; `\i. (x , v , pow_sigma_fan x V E v w i, pow_sigma_fan x V E v w (SUC i))`] sum_in_seg) THEN ASM_SIMP_TAC[] THEN SUBGOAL_THEN `(~(m = 0) /\ (!i j. i < j /\ j < m ==> ~(x:real^3,v:real^3,pow_sigma_fan (x:real^3) V E v w i,pow_sigma_fan (x:real^3) V E v w (SUC i) = x,v,pow_sigma_fan (x:real^3) V E v w j,pow_sigma_fan (x:real^3) V E v w (SUC j))))` ASSUME_TAC THENL[ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `(azim_dart o (\i. x:real^3,v:real^3,pow_sigma_fan (x:real^3) (V:real^3->bool) E v w i,pow_sigma_fan (x:real^3) V E v w (SUC i))) = (\i. azim (x:real^3) (v:real^3) (pow_sigma_fan (x:real^3) V E v w i) (pow_sigma_fan (x:real^3) V E v w (SUC i)))` ASSUME_TAC THENL[REWRITE_TAC[o_DEF;azim_dart]; ASM_SIMP_TAC[]]]);;

(* I will modify this, when this lemma is finised *)

let lemmaULEKUUB = prove (`!x:real^3 V:real^3->bool (E:(real^3->bool)->bool) (v:real^3) (w:real^3) (w1:real^3). fan (x,V,E) /\ (x,v,w,w1) IN D1 (x,V,E) ==> sum (0..card_node x V E (x,v,w,w1) - 1) (\i. azim x v (pow_sigma_fan x V E v w i) (pow_sigma_fan x V E v w (SUC i))) = &2 * pi`, CHEAT_TAC);;

(* I use a non precise statement as in the note, since I have not define the contravening hypermap, if you can convince other to change his task, I would like to work on this lemma, for the completion of my lemma, this lemma is essential to my lemma *)

let lemmaCDTETAT = prove (`!x:real^3 V:real^3->bool (E:(real^3->bool)->bool). fan (x,V,E) ==> (!d. d IN D1 (x,V,E) ==> &852 / &1000 <= azim_dart d /\ azim_dart d <= &19 / &10)`, CHEAT_TAC);;


let finite_nfan = prove (`!x V E v w w1. fan (x, V, E) /\ (x, v, w, w1) IN D1 (x, V, E) ==> FINITE (node (hypermap_of_fan (x, V, E)) (x, v, w, w1))`, REPEAT STRIP_TAC THEN REWRITE_TAC[node] THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`] n_hyp_of_fan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`] hyp_fan1) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`] hyp_fan3) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (ISPECL [`dart_fan (x:real^3, V:real^3->bool, E:(real^3->bool)->bool)` ; `n_fan x V E`; `(x:real^3, v:real^3, w:real^3, w1:real^3)`] fin_lem) THEN ASM_REWRITE_TAC[]);;

(* This one is for the completeness, actually, when you look at the fan part, you will see the hole in that *)

let azim_dart_nin_d1 = prove (`!x V E d. fan (x, V, E) /\ ~(d IN D1 (x, V, E)) ==> &1 <= azim_dart d`, CHEAT_TAC);; 

(* In this lemma, I state in a not precise way, as I have said, since I have not define the contravening. Also, I use a lemma, in the pishort.ml *)

let lemmaSZIPOAS = prove (`!x V E v w w1. fan (x, V, E) /\ (x, v, w, w1) IN D1 (x, V, E) ==> card_node x V E (x, v, w, w1) <= 7`, REPEAT STRIP_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`; `v:real^3` ;`w:real^3`; `w1:real^3`] lemmaULEKUUB) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`; `v:real^3` ;`w:real^3`; `w1:real^3`] alt_azim_fan_sum) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`; `v:real^3` ;`w:real^3`; `w1:real^3`] finite_nfan) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`] lemmaCDTETAT) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN (LABEL_TAC "fh1") THEN MP_TAC (SPECL [`&852 / &1000`; `x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`; `(x:real^3, v:real^3, w:real^3, w1:real^3)`] node_lbound_lm) THEN ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `!d:real^3#real^3#real^3#real^3. &852 / &1000 <= azim_dart d` ASSUME_TAC THENL[STRIP_TAC THEN ASM_CASES_TAC `(d:real^3#real^3#real^3#real^3) IN D1 (x:real^3, V:real^3->bool, E:(real^3->bool)->bool)` THENL[USE_THEN "fh1" (MP_TAC o SPEC `d:real^3#real^3#real^3#real^3`) THEN ASM_SIMP_TAC[]; MP_TAC (SPECL [`x:real^3`; `V:real^3->bool`; `E:(real^3->bool)->bool`; `(d:real^3#real^3#real^3#real^3)`] azim_dart_nin_d1) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]; ASM_REWRITE_TAC[] THEN MP_TAC (SPEC `card_node (x:real^3) (V:real^3->bool) (E:(real^3->bool)->bool) (x, v, w, w1)` bound_for_pi) THEN ASM_SIMP_TAC[]]);;
 


