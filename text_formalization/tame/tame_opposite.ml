(*Trieu Thi Diep*)

needs "hypermap.ml";;

(*
needs "Multivariate/flyspeck.ml";;
needs "general/sphere.ml";;
#use "thales_tactic.ml";;
(* needs "trig_spec.ml";; *)
#use "trig.ml";;
(* tarski *)
#use "hull.ml";;
#use "collect_geom_a.ml";;
#use  "collect_geom.ml";;
(*
collect_geom_spec.ml is incompatible with collect_geom.ml,
because of incompatible new_specifications, starting with
point_eq.

needs "collect_geom_spec.ml";; 
*)
(*
#use "volume.ml";;
#use "hypermap.ml";; (* loads with multivariate *)
*)
*)





let opposite_hypermap = new_definition `opposite_hypermap (H:(A)hypermap) = hypermap ((dart H),face_map H o node_map H , inverse(node_map H),inverse(face_map H))`;;

let edge_nondegenerate = new_definition `edge_nondegenerate (H:(A)hypermap)  
   <=> !(x:A).(x IN dart H) ==> ~ (edge_map H x = x)`;;

let no_loops = new_definition `no_loops (H:(A) hypermap) <=> ! (x:A) (y:A). x IN edge H y /\ x IN node H y ==> x = y`;;  

let hypermap_no_double_joins = new_definition (`hypermap_no_double_joins (H:(A) hypermap) <=> ! (x:A) (y:A) (z:A) (t:A) (u:A) (v:A). x IN node H z /\ y IN (edge H x INTER node H t) /\ ~ (x = y) /\ ~(z IN node H t) /\ u IN node H z /\ v IN (edge H u INTER node H t) /\ ~(u = v) ==>  x IN edge H u`);; 
 
let exceptional_face = new_definition `exceptional_face (H:(A)hypermap) (x:A) <=> CARD (face H x) >= 5`;;

let set_of_triangles_meeting_node = new_definition `set_of_triangles_meeting_node (H:(A)hypermap) (x:A) = {face H (y:A) |y | y IN dart H /\ CARD (face H y) = 3 /\  y IN node H x }`;;

let set_of_quadrilaterals_meeting_node = new_definition `set_of_quadrilaterals_meeting_node (H:(A)hypermap) (x:A) = {face (H:(A)hypermap) (y:A)|y | y IN dart H /\ CARD (face H y) = 4 /\ y IN node H x}`;;

let set_of_exceptional_meeting_node = new_definition `set_of_exceptional_meeting_node (H:(A)hypermap) (x:A) = {face H (y:A) | y | (y IN (dart H)) /\ (CARD (face H y) >= 5) /\ (y IN node H x)}`;;

let set_of_face_meeting_node = new_definition `set_of_face_meeting_node (H:(A)hypermap) (x:A) = {face H (y:A)|y| y IN dart H /\ y IN node H x}`;;

let type_of_node = new_definition `type_of_node (H:(A)hypermap) (x:A) =  (CARD (set_of_triangles_meeting_node H x), CARD (set_of_quadrilaterals_meeting_node H x), CARD (set_of_exceptional_meeting_node H x ))`;;

let node_type_exceptional_face = new_definition `node_type_exceptional_face (H:(A)hypermap) (x:A) <=>  exceptional_face H x /\ (CARD (node H x) = 6) ==> type_of_node H x = (5,0,1)`;;

let node_exceptional_face = new_definition `node_exceptional_face (H:(A)hypermap) (x:A) <=> exceptional_face H x ==> CARD (node H x) <= 6`;;

let tgt = new_definition `tgt = &1541 / &1000`;;

let b_tame = new_definition `b_tame p q = if p,q = 0,3 then &618 / &1000 else 
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

let d_tame = new_definition `d_tame n = if n = 3 then &0 else 
                      if n = 4 then &206 / &1000 else
                      if n = 5 then &483 / &1000 else 
                      if n = 6 then &760 / &1000 else tgt`;;

let a_tame = new_definition `a_tame = &63 / &100`;;

let weight =
  REWRITE_RULE[]
   (new_type_definition "weight" ("weight","we")
     (prove(`?f:(A->bool)->real. !x. f x >= &0`,EXISTS_TAC `(\x:(A->bool). &0)` THEN REAL_ARITH_TAC)));;

let total_weight = new_definition `total_weight (H:(A)hypermap) (w:(A->bool)->real) = sum (face_set H) w`;;

let adm_1 = new_definition `adm_1 (H:(A)hypermap) (w:(A->bool)->real) <=> (!x:A. w (face H x)  >= d_tame (CARD (face H x)))`;;

let adm_2 = new_definition `adm_2 (H:(A)hypermap) (w:(A->bool)->real) <=> (!x:A. (CARD (set_of_exceptional_meeting_node H x) = 0) ==> ((sum (set_of_face_meeting_node H x) w) >= (b_tame (CARD (set_of_triangles_meeting_node H x)) (CARD (set_of_quadrilaterals_meeting_node H x)))))`;;

let adm_3 = new_definition `adm_3 (H:(A)hypermap) (w:(A->bool)->real) <=> (!x:A. type_of_node H x = 5, 0, 1 ==> (sum (set_of_triangles_meeting_node H x) w)  >= a_tame)`;;

let admissible_weight = new_definition `admissible_weight (H:(A)hypermap) (w:(A->bool)->real) <=> adm_1 H w /\ adm_2 H w /\ adm_3 H w`;;

let tame_1 = new_definition `tame_1 (H:(A)hypermap) <=> plain_hypermap (H:(A)hypermap) /\ planar_hypermap (H:(A)hypermap)`;;

let tame_2 = new_definition `tame_2 (H:(A)hypermap) <=> connected_hypermap H /\ simple_hypermap H`;;

let tame_3 = new_definition `tame_3 (H:(A)hypermap)  <=>  edge_nondegenerate H `;;

let tame_4 = new_definition `tame_4 (H:(A)hypermap)  <=> no_loops H`;;

let tame_5 = new_definition `tame_5 (H:(A)hypermap)  <=> hypermap_no_double_joins H `;;

let tame_8 = new_definition `tame_8 (H:(A)hypermap)  <=> number_of_faces H >= 3`;;

let tame_9o = new_definition `tame_9o (H:(A)hypermap)  <=> (!(x:A). CARD (face H x) >= 3 /\ CARD (face H x) <= 6)`;;

let tame_10 = new_definition `tame_10 (H:(A)hypermap) <=> number_of_nodes H = 13 \/ number_of_nodes H = 14`;;

let tame_11o = new_definition `tame_11o (H:(A)hypermap) <=> (!(x:A). CARD (node H x) >= 3 /\ CARD (node H x) <= 7)`;;


let tame_12o = new_definition `tame_12o (H:(A)hypermap)  <=> (! (x:A). node_type_exceptional_face H x /\ node_exceptional_face H x)`;;

let tame_13 = new_definition `tame_13 (H:(A)hypermap) <=> (?(w:(A->bool)->real). admissible_weight H w /\ total_weight H w <= tgt)`;;

let tame_hypermap = new_definition `tame_hypermap (H:(A)hypermap) <=> tame_1 H /\ tame_2 H /\ tame_3 H /\ tame_4 H /\ tame_5 H /\ tame_8 H /\ tame_9o H /\ tame_10 H /\ tame_11o H /\ tame_12o H /\ tame_13 H` ;;


let tuple_opposite_hypermap = prove 
(`!(H:(A)hypermap). tuple_hypermap (opposite_hypermap H) = ((dart H),face_map H o node_map H , inverse(node_map H),inverse(face_map H))`,
GEN_TAC THEN REWRITE_TAC[opposite_hypermap] THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) 
THEN REPEAT STRIP_TAC THEN ABBREV_TAC `D = dart (H:(A)hypermap)` THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)`
THEN SUBGOAL_THEN `FINITE (FST ((D:A->bool),(f:A->A) o (n:A->A),inverse n,inverse f))` ASSUME_TAC THENL [ASM_MESON_TAC[FST];  
SUBGOAL_THEN `FST (SND ((D:A->bool),(f:A->A) o (n:A->A),inverse n,inverse f)) permutes FST ((D:A->bool),(f:A->A) o (n:A->A),inverse n,inverse f)` ASSUME_TAC THENL [ASM_REWRITE_TAC[SND;FST] THEN ASM_MESON_TAC[PERMUTES_COMPOSE];
SUBGOAL_THEN `FST (SND (SND ((D:A->bool),(f:A->A) o (n:A->A),inverse n,inverse f))) permutes FST ((D:A->bool),(f:A->A) o (n:A->A),inverse n,inverse f)` ASSUME_TAC THENL [ASM_REWRITE_TAC[SND;FST] THEN ASM_MESON_TAC[PERMUTES_INVERSE]; 
SUBGOAL_THEN `SND (SND (SND ((D:A->bool),(f:A->A) o (n:A->A),inverse n,inverse f))) permutes FST ((D:A->bool),(f:A->A) o (n:A->A),inverse n,inverse f)` ASSUME_TAC THENL [ASM_REWRITE_TAC[SND;FST] THEN ASM_MESON_TAC[PERMUTES_INVERSE]; 
SUBGOAL_THEN ` FST (SND ((D:A->bool),(f:A->A) o (n:A->A),inverse n,inverse f)) o FST (SND (SND ((D:A->bool),(f:A->A) o (n:A->A),inverse n,inverse f))) o SND (SND (SND ((D:A->bool),(f:A->A) o (n:A->A),inverse n,inverse f))) = I` ASSUME_TAC 
THENL [ASM_REWRITE_TAC[SND;FST;o_ASSOC] THEN SUBGOAL_THEN `(((f:A->A) o (n:A->A)) o inverse n) o inverse f = (f o n o inverse n) o inverse f` ASSUME_TAC 
THENL [MESON_TAC[o_ASSOC]; ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `(n:A->A) o inverse n = I` ASSUME_TAC 
THENL [ASM_MESON_TAC[PERMUTES_INVERSES_o];ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[I_O_ID;PERMUTES_INVERSES_o] ]]; 
ASM_MESON_TAC[hypermap_tybij]    ]] ]]]);; 


let POWER_INVERSE_o = prove (`!(p:A->A) (s:A->bool) (n:num) (x:A). p permutes s ==> (p POWER n) ((inverse p POWER n) x) = x`,
REPLICATE_TAC 2 GEN_TAC THEN INDUCT_TAC 
THENL [ASM_MESON_TAC[POWER_0;I_THM];
SUBGOAL_THEN `!(x:A). (p POWER (SUC n:num)) (((inverse p POWER SUC n)) (x:A)) =((p:A->A) o (p POWER (n:num))) (((inverse p POWER SUC n)) (x:A))` ASSUME_TAC
THENL [ REWRITE_TAC[COM_POWER];
SUBGOAL_THEN `!(x:A).((p:A->A) o (p POWER (n:num))) (((inverse p POWER SUC n)) (x:A)) = ((p:A->A) o (p POWER (n:num))) (((inverse p POWER n) o (inverse p)) (x:A))`ASSUME_TAC 
THENL [
    REWRITE_TAC[ADD1] 
    THEN ASM_MESON_TAC[addition_exponents;POWER_1];ASM_REWRITE_TAC[o_ASSOC;o_THM]
THEN UNDISCH_TAC `!(x:A).(p:A->A) permutes (s:A->bool) ==> (p POWER (n:num)) ((inverse p POWER n)  x) =  x` 
THEN DISCH_THEN (LABEL_TAC "H1")
THEN GEN_TAC THEN DISCH_TAC
THEN USE_THEN "H1" (ASSUME_TAC o SPEC `inverse (p:A->A) (x:A)`)
THEN SUBGOAL_THEN `((p:A->A) POWER (n:num)) ((inverse p POWER n) (inverse p (x:A))) = inverse p x ` ASSUME_TAC 
THENL [
    ASM_MESON_TAC[]; 
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PERMUTES_INVERSES_o;o_THM;I_THM]] ]]]);; 


let opposite_hypermap_plain = prove ( `!(H:(A)hypermap).(plain_hypermap (H:(A)hypermap)) ==> plain_hypermap (opposite_hypermap (H:(A)hypermap))`,
GEN_TAC THEN REWRITE_TAC[plain_hypermap;opposite_hypermap] THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) 
THEN REPEAT STRIP_TAC THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap)
THEN REWRITE_TAC[opposite_hypermap] THEN DISCH_TAC THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` THEN ABBREV_TAC `n = node_map (H:(A)hypermap)`
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` THEN REWRITE_TAC[edge_map] 
THEN ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `((f:A->A) o (n:A->A)) o f o n = f o (n o f) o n` ASSUME_TAC 
THENL [REWRITE_TAC[o_ASSOC]; SUBGOAL_THEN `(e o (e:A->A) o (n:A->A) o (f:A->A) = e)` ASSUME_TAC 
THENL [UNDISCH_TAC `(e:A->A) o (n:A->A) o (f:A->A) = I` THEN ASM_MESON_TAC[LEFT_MULT_MAP;I_O_ID];  
SUBGOAL_THEN `(n:A->A) o (f:A->A) = (e:A->A)` ASSUME_TAC 
THENL [ASM_MESON_TAC[I_O_ID;o_ASSOC];ASM_REWRITE_TAC[] 
THEN SUBGOAL_THEN `(e:A->A) o (n:A->A) = inverse (f:A->A)` ASSUME_TAC 
THENL [ UNDISCH_TAC `(e:A->A) o (n:A->A) o (f:A->A) = I` 
THEN SUBGOAL_THEN `(e:A->A) o (n:A->A) permutes (D:A->bool) ` ASSUME_TAC 
THENL [ ASM_MESON_TAC[PERMUTES_COMPOSE];ASM_MESON_TAC[o_ASSOC;RIGHT_INVERSE_EQUATION;I_O_ID]]; 
ASM_MESON_TAC[PERMUTES_INVERSES_o]   ] ]]]);;


let opposite_hypermap_simple = prove ( `!(H:(A)hypermap). simple_hypermap H ==> simple_hypermap (opposite_hypermap H)`,
GEN_TAC THEN REWRITE_TAC[simple_hypermap;opposite_hypermap;face;node] 
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap) 
THEN REWRITE_TAC[opposite_hypermap] THEN  ABBREV_TAC `D = dart (H:(A)hypermap)`  
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` THEN  ABBREV_TAC `n = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` THEN  REWRITE_TAC[node;dart;face;node_map;face_map] 
THEN  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN  REPEAT STRIP_TAC THEN  REWRITE_TAC [orbit_map; EXTENSION; IN_ELIM_THM] 
THEN  GEN_TAC THEN EQ_TAC  THENL [ REWRITE_TAC [INTER;IN_ELIM_THM] THEN REPEAT STRIP_TAC 
THEN  SUBGOAL_THEN `((n:A->A) POWER (n':num)) (x':A) = (x:A)` ASSUME_TAC 
THENL [ ASM_MESON_TAC[o_THM;POWER_INVERSE_o];SUBGOAL_THEN `((f:A->A) POWER (n'':num)) (x':A) = (x:A)` ASSUME_TAC 
THENL [ASM_MESON_TAC[o_THM;POWER_INVERSE_o];SUBGOAL_THEN `(x:A) IN (orbit_map (n:A->A) (x':A) INTER orbit_map (f:A->A) x')` ASSUME_TAC 
THENL [REWRITE_TAC[orbit_map;IN;IN_INTER;IN_ELIM_THM] THEN ASM_MESON_TAC[orbit_sym];
SUBGOAL_THEN `(x':A) IN (orbit_map (n:A->A) (x:A) INTER orbit_map (f:A->A) x)` ASSUME_TAC 
THENL [REWRITE_TAC[IN_INTER] THEN STRIP_TAC THENL [ASM_MESON_TAC[orbit_sym;IN_INTER]; ASM_MESON_TAC[orbit_sym;IN_INTER] ]; 
SUBGOAL_THEN `(orbit_map (n:A->A) (x:A) INTER orbit_map (f:A->A) x) = {x}` ASSUME_TAC 
THENL [FIRST_ASSUM (ASSUME_TAC o SPEC `x:A`) THEN ASM_MESON_TAC[];ASM_MESON_TAC[] ]]]]] ;
REWRITE_TAC [INTER;IN_ELIM_THM;orbit_map] THEN STRIP_TAC THEN SUBGOAL_THEN ` (x':A) = (x:A)` ASSUME_TAC 
THENL [ASM_MESON_TAC[IN_SING];REPEAT STRIP_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `0` 
THEN REWRITE_TAC[POWER_0] THEN STRIP_TAC THENL [ARITH_TAC ;MESON_TAC[I_THM] ] ;EXISTS_TAC `0` THEN REWRITE_TAC[POWER_0] 
THEN STRIP_TAC THENL [ARITH_TAC;ASM_MESON_TAC[I_THM]   ]]]]);; 


let opposite_hypermap_connected = prove (
`!(H:(A)hypermap).connected_hypermap H ==> connected_hypermap (opposite_hypermap H)`,
GEN_TAC THEN 
(REWRITE_TAC[connected_hypermap;number_of_components;component_set;opposite_hypermap])
);;



let opposite_nondegenerate = prove (`!(H:(A)hypermap). plain_hypermap H /\ edge_nondegenerate H ==> edge_nondegenerate (opposite_hypermap H) `,
GEN_TAC THEN REWRITE_TAC[plain_hypermap;edge_nondegenerate;opposite_hypermap] 
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap)
THEN REWRITE_TAC[opposite_hypermap] THEN ABBREV_TAC `D = dart (H:(A)hypermap)` THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)`
THEN REWRITE_TAC[edge_map;dart] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC
THEN SUBGOAL_THEN `(((n:A->A) o (f:A->A)) o n) (x:A) = n x` ASSUME_TAC 
THENL [UNDISCH_TAC `((f:A->A) o (n:A->A)) (x:A) = x` THEN DISCH_THEN (LABEL_TAC "H1") THEN USE_THEN "H1" (ASSUME_TAC o(AP_TERM `e:A->A`)) THEN ASM_MESON_TAC[o_THM;o_ASSOC];
SUBGOAL_THEN `((inverse (e:A->A)) o (n:A->A)) (x:A) = n x ` (LABEL_TAC "H2")
THENL [ASM_MESON_TAC[LEFT_INVERSE_EQUATION;I_O_ID] ;
USE_THEN "H2" (ASSUME_TAC o (AP_TERM `(e:A->A) o e`))
THEN SUBGOAL_THEN `(e:A->A) ((n:A->A) (x:A)) = (e o e) (n x)` ASSUME_TAC
THENL [ASM_MESON_TAC[PERMUTES_INVERSES_o;o_THM;o_ASSOC;I_O_ID];
SUBGOAL_THEN `(e:A->A) ((n:A->A) (x:A)) = n x` ASSUME_TAC
THENL [ASM_MESON_TAC[I_THM]; SUBGOAL_THEN `(n:A->A) (x:A) IN (D:A->bool)` ASSUME_TAC 
THENL [ASM_MESON_TAC[permutes]; ASM_MESON_TAC[] ]]]]] );;

let inverse_same_orbit = prove (`!(p:A->A) (s:A->bool) (y:A) (x:A). FINITE s /\ p permutes s /\ y IN orbit_map p x ==> y IN orbit_map (inverse p) x `,
REPEAT GEN_TAC THEN REWRITE_TAC[orbit_map;IN_ELIM_THM] THEN STRIP_TAC 
THEN SUBGOAL_THEN `(inverse (p:A->A) POWER n ) (y:A) = x` ASSUME_TAC
THENL [ MP_TAC (SPECL [`inverse (p:A->A)`;`s:A->bool`;`n:num`;`x:A`] POWER_INVERSE_o) 
THEN ASM_MESON_TAC[o_THM;o_ASSOC;PERMUTES_INVERSE_INVERSE;PERMUTES_INVERSE;LEFT_MULT_MAP];
SUBGOAL_THEN `(x:A) IN (orbit_map (inverse (p:A->A)) y)` ASSUME_TAC
THENL [ONCE_ASM_REWRITE_TAC[orbit_map;IN_ELIM_THM] THEN REWRITE_TAC[IN_ELIM_THM] 
THEN EXISTS_TAC `n:num` THEN ASM_MESON_TAC[];
SUBGOAL_THEN `(y:A) IN (orbit_map (inverse (p:A->A)) x)` ASSUME_TAC
THENL [ASM_MESON_TAC[orbit_sym;PERMUTES_INVERSE];
UNDISCH_TAC `(y:A) IN (orbit_map (inverse (p:A->A)) (x:A))` THEN REWRITE_TAC[orbit_map;IN_ELIM_THM] ]]]);;


let the_same_orbit = prove ( `!(p:A->A) (s:A->bool) (x:A). FINITE s /\ p permutes s ==> orbit_map p x = orbit_map (inverse p) x`,
REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_MESON_TAC[PERMUTES_INVERSE;inverse_same_orbit;SUBSET_ANTISYM_EQ;PERMUTES_INVERSE_INVERSE;SUBSET] );;


let the_SUBSET_set_of_orbits = prove ( `!(p:A->A) (s:A->bool). FINITE s /\ p permutes s ==> set_of_orbits s p SUBSET set_of_orbits s (inverse p)`,
REPEAT GEN_TAC THEN REWRITE_TAC[set_of_orbits;SUBSET;IN_ELIM_THM;EXTENSION] THEN REPEAT STRIP_TAC 
THEN SUBGOAL_THEN `(x:A->bool) = orbit_map (inverse (p:A->A)) (x':A)` ASSUME_TAC
THENL [REWRITE_TAC[EXTENSION] THEN GEN_TAC THEN EQ_TAC 
THENL [FIRST_ASSUM (ASSUME_TAC o (SPEC `x'':A`)) THEN DISCH_TAC 
THEN (ASM_MESON_TAC[inverse_same_orbit]); (FIRST_ASSUM (ASSUME_TAC o (SPEC `x'':A`))) THEN  DISCH_TAC 
THEN ASM_MESON_TAC[inverse_same_orbit;PERMUTES_INVERSE_INVERSE;PERMUTES_INVERSE]]; EXISTS_TAC `(x':A)` THEN ASM_MESON_TAC[] ]);;


let the_same_set_of_orbits = prove ( `!(p:A->A) (s:A->bool). FINITE s /\ p permutes s ==> set_of_orbits s p = set_of_orbits s (inverse p)`,
REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_MESON_TAC[SUBSET_ANTISYM_EQ;the_SUBSET_set_of_orbits;PERMUTES_INVERSE;PERMUTES_INVERSE_INVERSE]);;


let FINITE_set_of_orbits = prove ( `!(p:A->A) (s:A->bool). FINITE s /\ p permutes s ==> FINITE (set_of_orbits s p)`,
REPEAT GEN_TAC THEN REWRITE_TAC[set_of_orbits] THEN  DISCH_TAC
THEN SUBGOAL_THEN `{orbit_map (p:A->A) (x:A) | x IN s} = IMAGE (orbit_map p) s` ASSUME_TAC
THENL [REWRITE_TAC[SIMPLE_IMAGE;IMAGE;EXTENSION;IN_ELIM_THM]; ASM_MESON_TAC[FINITE_IMAGE] ]);;


let the_same_CARD = prove ( `!(p:A->A) (s:A->bool).FINITE s /\ p permutes s ==> CARD (set_of_orbits s p) = CARD (set_of_orbits s (inverse p))`,
REPEAT GEN_TAC THEN MESON_TAC[FINITE_set_of_orbits;the_same_set_of_orbits;the_SUBSET_set_of_orbits;PERMUTES_INVERSE]);;


let edge_CARD_dart = prove (`!(s:A->bool) (p:A->A).
FINITE s /\ p permutes s /\ p o p = I /\ (!x. x IN s ==> ~(p x = x)) ==> CARD s = 2 * number_of_orbits s p`,
REPEAT GEN_TAC THEN MESON_TAC[lemma_nondegenerate_convolution;lemma_orbits_eq]);;


let opposite_planar = prove ( `!(H:(A)hypermap). connected_hypermap H /\ planar_hypermap H /\ edge_nondegenerate H /\ plain_hypermap H ==> planar_hypermap (opposite_hypermap H)`,
GEN_TAC THEN REWRITE_TAC[connected_hypermap;opposite_hypermap;tuple_opposite_hypermap;edge_nondegenerate;plain_hypermap]
THEN MP_TAC (SPEC `H:(A)hypermap` opposite_nondegenerate) THEN MP_TAC (SPEC `H:(A)hypermap` opposite_hypermap_plain)
THEN MP_TAC (SPEC `H:(A)hypermap` opposite_hypermap_connected) THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma)
THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap) THEN REWRITE_TAC[opposite_hypermap]
THEN ABBREV_TAC `D = dart (H:(A)hypermap)` THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)`
THEN REWRITE_TAC[planar_hypermap;number_of_nodes;number_of_faces;number_of_edges;node_set;edge_set;face_set]
THEN STRIP_TAC THEN ASM_REWRITE_TAC[connected_hypermap;plain_hypermap;edge_nondegenerate;opposite_hypermap;face_map;edge_map;node_map;dart]
THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN `CARD (set_of_orbits (D:A->bool) (inverse (n:A->A))) = CARD (set_of_orbits (D:A->bool) (n:A->A))` ASSUME_TAC
THENL [ ASM_MESON_TAC[the_same_CARD];
SUBGOAL_THEN `CARD (set_of_orbits (D:A->bool) (inverse (f:A->A))) = CARD (set_of_orbits (D:A->bool) (f:A->A))` ASSUME_TAC
THENL [ASM_MESON_TAC[the_same_CARD];
SUBGOAL_THEN `CARD (D:A->bool) = 2 * CARD (set_of_orbits D (e:A->A))` ASSUME_TAC
THENL [ASM_MESON_TAC[edge_CARD_dart;number_of_orbits];
SUBGOAL_THEN `CARD (D:A->bool) = 2 * CARD (set_of_orbits D  ((f:A->A) o (n:A->A)))` ASSUME_TAC
THENL [ASM_MESON_TAC[edge_CARD_dart;number_of_orbits;PERMUTES_COMPOSE]; 
SUBGOAL_THEN `2 * CARD (set_of_orbits (D:A->bool) (e:A->A)) = 2 * CARD (set_of_orbits D ((f:A->A) o (n:A->A)))` ASSUME_TAC
THENL [ASM_MESON_TAC[];
SUBGOAL_THEN ` CARD (set_of_orbits (D:A->bool) (e:A->A)) =  CARD (set_of_orbits D ((f:A->A) o (n:A->A)))` ASSUME_TAC
THENL [SUBGOAL_THEN `~ (2 = 0)` ASSUME_TAC THENL [ARITH_TAC; ASM_MESON_TAC[EQ_MULT_LCANCEL]];ASM_MESON_TAC[] ]]]]]]);;


let CARD_faces1 = prove (`! (H:(A)hypermap). tame_8 H  ==> tame_8 (opposite_hypermap H) `,
GEN_TAC THEN REWRITE_TAC[number_of_faces;opposite_hypermap;tuple_opposite_hypermap;tame_8] 
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap)
THEN REWRITE_TAC[opposite_hypermap] THEN ABBREV_TAC `D = dart (H:(A)hypermap)` THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` THEN REWRITE_TAC[face_set]
THEN STRIP_TAC THEN ASM_REWRITE_TAC[face_map;dart] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[the_same_CARD]);;


let CARD_in_face = prove ( `!(H:(A)hypermap) . tame_9o H   ==> tame_9o (opposite_hypermap H) `,
REPEAT GEN_TAC THEN REWRITE_TAC[face;opposite_hypermap;tuple_opposite_hypermap;tame_9o]
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap)
THEN REWRITE_TAC[opposite_hypermap] THEN ABBREV_TAC `D = dart (H:(A)hypermap)` THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)`
THEN REWRITE_TAC[face_set] THEN STRIP_TAC THEN ASM_REWRITE_TAC[face_map;dart] THEN REPEAT STRIP_TAC 
THEN ASM_MESON_TAC[the_same_orbit] THEN ASM_MESON_TAC[the_same_orbit]);;


let CARD_nodes = prove ( `! (H:(A)hypermap). tame_10 H ==> tame_10 (opposite_hypermap H)`,
GEN_TAC THEN REWRITE_TAC[number_of_nodes;opposite_hypermap;tuple_opposite_hypermap;tame_10]
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap)
THEN REWRITE_TAC[opposite_hypermap] THEN ABBREV_TAC `D = dart (H:(A)hypermap)` THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` 
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)`
THEN REWRITE_TAC[node_set] THEN STRIP_TAC THEN  ASM_REWRITE_TAC[node_map;dart] THEN REPEAT STRIP_TAC
THENL [ DISJ1_TAC THEN ASM_MESON_TAC[the_same_CARD]; DISJ2_TAC THEN ASM_MESON_TAC[the_same_CARD] ]);;


let CARD_in_node = prove ( `!(H:(A)hypermap) . tame_11o H  ==>  tame_11o (opposite_hypermap H) `,
REPEAT GEN_TAC THEN REWRITE_TAC[node;opposite_hypermap;tuple_opposite_hypermap;tame_11o]
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap)
THEN REWRITE_TAC[opposite_hypermap] THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` THEN ABBREV_TAC `n = node_map (H:(A)hypermap)`
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` THEN REWRITE_TAC[node_set] THEN STRIP_TAC
THEN ASM_REWRITE_TAC[node_map;dart] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[the_same_orbit] THEN ASM_MESON_TAC[the_same_orbit]);;


let lemma_dart_in_edge = prove ( `!(p:A->A) (s:A->bool) (x:A) (y:A). FINITE s /\ p permutes s /\ ~(x = y) /\ (p o p = I) /\  x IN orbit_map p y  ==> x = p y `,
REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN UNDISCH_TAC `(x:A) IN orbit_map (p:A->A) (y:A)`
THEN ASM_REWRITE_TAC[orbit_map;IN_ELIM_THM] THEN STRIP_TAC
THEN SUBGOAL_THEN `(p:A->A) POWER 2 = I` ASSUME_TAC 
THENL [ ASM_MESON_TAC[POWER_2];SUBGOAL_THEN `EVEN (n:num) \/ ODD n` ASSUME_TAC
THENL [ASM_MESON_TAC[EVEN_OR_ODD];FIRST_X_ASSUM (DISJ_CASES_TAC) 
THENL [SUBGOAL_THEN `? (j:num). (n:num) = 2 * j` ASSUME_TAC THENL [ASM_MESON_TAC[EVEN_EXISTS];
FIRST_X_ASSUM CHOOSE_TAC THEN SUBGOAL_THEN `((p:A->A) POWER (2 * (j:num)))  = I` (LABEL_TAC "H2")
THENL [ASM_MESON_TAC[power_unit_map;MULT_SYM];SUBGOAL_THEN `x:A = y:A` ASSUME_TAC
THENL [UNDISCH_TAC `(x:A) = ((p:A->A) POWER (n:num)) (y:A)` THEN ONCE_ASM_REWRITE_TAC[] THEN DISCH_TAC
THEN SUBGOAL_THEN `((p:A->A) POWER (2 * (j:num))) (y:A)  = y` ASSUME_TAC THENL [ASM_MESON_TAC[RIGHT_MULT_MAP;I_THM];
ASM_MESON_TAC[]];ASM_MESON_TAC[] ]]]; SUBGOAL_THEN `? (j:num). (n:num) = 2 * j + 1` ASSUME_TAC 
THENL [ ASM_MESON_TAC[ODD_EXISTS;ADD1];FIRST_X_ASSUM CHOOSE_TAC 
THEN SUBGOAL_THEN `((p:A->A) POWER (2 * (j:num)))  = I` (LABEL_TAC "H2") 
THENL [ASM_MESON_TAC[power_unit_map;MULT_SYM];
SUBGOAL_THEN `((p:A->A) POWER (2 * (j:num) + 1))  = p` (LABEL_TAC "H3")
THENL [ASM_MESON_TAC[addition_exponents;I_O_ID;POWER_1];ASM_MESON_TAC[] ]]]]]]);;

let thm_no_loops = prove ( `!(H:(A)hypermap).plain_hypermap H /\ no_loops H ==> no_loops (opposite_hypermap H)`,
GEN_TAC THEN REWRITE_TAC[plain_hypermap;opposite_hypermap;edge;node;no_loops]
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` opposite_hypermap_plain)
THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap) THEN REWRITE_TAC[opposite_hypermap]
THEN ABBREV_TAC `D = dart (H:(A)hypermap)` THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)`
THEN DISCH_TAC THEN ASM_REWRITE_TAC[plain_hypermap;edge_map;node_map;face_map] THEN REPEAT STRIP_TAC
THEN ASM_CASES_TAC `x : A = y : A`
THENL [FIRST_ASSUM ACCEPT_TAC;
SUBGOAL_THEN `(x:A) = ((f:A->A) o (n:A->A)) (y:A)` ASSUME_TAC 
THENL [ ASM_MESON_TAC[lemma_dart_in_edge;PERMUTES_COMPOSE];
SUBGOAL_THEN `?(k:num).(x:A) = (inverse (n:A->A) POWER (k:num)) (y:A)` ASSUME_TAC
THENL [UNDISCH_TAC `(x:A) IN orbit_map (inverse (n:A->A)) (y:A)` THEN REWRITE_TAC[IN_ELIM_THM;orbit_map] THEN MESON_TAC[];
FIRST_X_ASSUM CHOOSE_TAC THEN SUBGOAL_THEN `(y:A) = ((n:A->A) POWER (k:num)) (x:A)` ASSUME_TAC
THENL [ASM_MESON_TAC[PERMUTES_INVERSE; POWER_INVERSE_o];
ABBREV_TAC `x1 = (n:A->A) (x:A)` THEN POP_ASSUM (ASSUME_TAC o (SYM)) THEN ABBREV_TAC `y1 = (n:A->A) (y:A)`
THEN POP_ASSUM (ASSUME_TAC o (SYM)) THEN SUBGOAL_THEN `(x1:A) = (n:A->A) (((f:A->A) o (n:A->A)) (y:A))` (LABEL_TAC "H2")
THENL [ASM_MESON_TAC[];
SUBGOAL_THEN `(n:A->A) (((f:A->A) o (n:A->A)) (y:A)) = (n o f) (y1: A)` (LABEL_TAC "H3")
THENL [ASM_MESON_TAC[o_THM;o_ASSOC];
SUBGOAL_THEN `(n:A->A) o (f:A->A) = (e:A->A)` ASSUME_TAC
THENL [ASM_MESON_TAC[cyclic_maps;INVERSE_UNIQUE_o;o_ASSOC];
SUBGOAL_THEN `(x1:A) = (e:A->A) (y1:A)` ASSUME_TAC
THENL [ASM_MESON_TAC[];
SUBGOAL_THEN `(y1:A) = ((n:A->A) POWER ((k:num) + 1)) (x:A)` ASSUME_TAC
THENL [ASM_MESON_TAC[lemma_add_exponent_function;ADD_SYM;POWER_1];
SUBGOAL_THEN `(y1:A) = ((n:A->A) POWER (k:num)) (x1:A)` ASSUME_TAC
THENL [ASM_MESON_TAC[lemma_add_exponent_function;POWER_1];
SUBGOAL_THEN `(x1:A) IN orbit_map e (y1:A)` ASSUME_TAC
THENL [ASM_MESON_TAC[POWER_1;in_orbit_lemma];
SUBGOAL_THEN `(x1:A) IN orbit_map (n:A->A) (y1:A)` ASSUME_TAC
THENL [ASM_MESON_TAC[in_orbit_lemma;orbit_sym];
SUBGOAL_THEN `(x1:A) = (y1:A)` ASSUME_TAC
THENL [ASM_MESON_TAC[];
ASM_MESON_TAC[PERMUTES_INVERSES_o;INJECTIVE_INVERSE_o] ]]]]]]]]]]]]]);;


let the_SAME_orbit_triangles = prove (`!(H:(A)hypermap) (x:A). set_of_triangles_meeting_node H x =  set_of_triangles_meeting_node (opposite_hypermap H) x`, REPEAT GEN_TAC THEN REWRITE_TAC[set_of_triangles_meeting_node;opposite_hypermap;SUBSET;IN_ELIM_THM;EXTENSION;SUBSET_ANTISYM_EQ]
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap)
THEN REWRITE_TAC[opposite_hypermap] THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` THEN ABBREV_TAC `n = node_map (H:(A)hypermap)`
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` THEN STRIP_TAC THEN ASM_REWRITE_TAC[dart;node;face]
THEN ASM_REWRITE_TAC[node_map;face_map;dart] THEN REPEAT STRIP_TAC THEN EQ_TAC
THENL [REPEAT STRIP_TAC THEN EXISTS_TAC `y:A` THEN CONJ_TAC
THENL [ASM_MESON_TAC[the_same_orbit];ASM_MESON_TAC[the_same_orbit]];
REPEAT STRIP_TAC THEN EXISTS_TAC `y:A` THEN CONJ_TAC
THENL [ASM_MESON_TAC[the_same_orbit];ASM_MESON_TAC[the_same_orbit] ] ]);;



let the_SAME_orbit_quadrilaterals = prove (`!(H:(A)hypermap) (x:A). set_of_quadrilaterals_meeting_node H x =  set_of_quadrilaterals_meeting_node (opposite_hypermap H) x`,
REPEAT GEN_TAC THEN REWRITE_TAC[set_of_quadrilaterals_meeting_node;opposite_hypermap;SUBSET;IN_ELIM_THM;EXTENSION;SUBSET_ANTISYM_EQ]
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN  MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap)
THEN REWRITE_TAC[opposite_hypermap] THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` THEN ABBREV_TAC `n = node_map (H:(A)hypermap)`
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` THEN STRIP_TAC THEN ASM_REWRITE_TAC[dart;node;face]
THEN ASM_REWRITE_TAC[node_map;face_map;dart] THEN REPEAT STRIP_TAC THEN EQ_TAC
THENL [REPEAT STRIP_TAC THEN EXISTS_TAC `y:A` THEN CONJ_TAC
THENL [ASM_MESON_TAC[the_same_orbit];ASM_MESON_TAC[the_same_orbit]];
REPEAT STRIP_TAC THEN EXISTS_TAC `y:A` THEN CONJ_TAC
THENL [ASM_MESON_TAC[the_same_orbit];ASM_MESON_TAC[the_same_orbit] ]]);;
 
let the_SAME_orbit_exceptional = prove ( `!(H:(A)hypermap) (x:A). set_of_exceptional_meeting_node H x =  set_of_exceptional_meeting_node (opposite_hypermap H) x`,
REPEAT GEN_TAC THEN REWRITE_TAC[set_of_exceptional_meeting_node;opposite_hypermap;SUBSET;IN_ELIM_THM;EXTENSION;SUBSET_ANTISYM_EQ]
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap)
THEN REWRITE_TAC[opposite_hypermap] THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` THEN ABBREV_TAC `n = node_map (H:(A)hypermap)`
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` THEN STRIP_TAC THEN ASM_REWRITE_TAC[dart;node;face]
THEN ASM_REWRITE_TAC[node_map;face_map;dart] THEN REPEAT STRIP_TAC THEN EQ_TAC
THENL [REPEAT STRIP_TAC THEN EXISTS_TAC `y:A` THEN CONJ_TAC 
THENL [ASM_MESON_TAC[the_same_orbit];ASM_MESON_TAC[the_same_orbit]];
REPEAT STRIP_TAC THEN EXISTS_TAC `y:A` THEN CONJ_TAC
THENL [ASM_MESON_TAC[the_same_orbit];ASM_MESON_TAC[the_same_orbit]]]);;


let the_SAME_orbit_face = prove (`!(H:(A)hypermap) (x:A). set_of_face_meeting_node H x =  set_of_face_meeting_node (opposite_hypermap H) x`,
REPEAT GEN_TAC THEN REWRITE_TAC[set_of_face_meeting_node;opposite_hypermap;SUBSET;IN_ELIM_THM;EXTENSION;SUBSET_ANTISYM_EQ]
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap)
THEN REWRITE_TAC[opposite_hypermap] THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` THEN ABBREV_TAC `n = node_map (H:(A)hypermap)`
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` THEN STRIP_TAC THEN ASM_REWRITE_TAC[dart;node;face]
THEN ASM_REWRITE_TAC[node_map;face_map;dart] THEN REPEAT STRIP_TAC THEN EQ_TAC
THENL [REPEAT STRIP_TAC THEN EXISTS_TAC `y:A` THEN CONJ_TAC
THENL [ASM_MESON_TAC[the_same_orbit];ASM_MESON_TAC[the_same_orbit]];
REPEAT STRIP_TAC THEN EXISTS_TAC `y:A` THEN CONJ_TAC
THENL [ASM_MESON_TAC[the_same_orbit];ASM_MESON_TAC[the_same_orbit] ]]);;


let node_opposite_exceptional_face = prove (`!(H:(A)hypermap) (x:A) . node_exceptional_face H x ==> node_exceptional_face (opposite_hypermap H) x`,
GEN_TAC THEN REWRITE_TAC[exceptional_face;node;opposite_hypermap;tuple_opposite_hypermap;face; node_exceptional_face]
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap)
THEN REWRITE_TAC[opposite_hypermap] THEN ABBREV_TAC `D = dart (H:(A)hypermap)`
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` 
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` THEN STRIP_TAC THEN ASM_REWRITE_TAC[node_map;dart;face_map]
THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN `CARD (orbit_map (n:A->A) (x:A)) <= 6` ASSUME_TAC
THENL [SUBGOAL_THEN `CARD (orbit_map (f:A->A) (x:A)) >= 5` ASSUME_TAC THENL [ASM_MESON_TAC[the_same_orbit];
ASM_MESON_TAC[]];ASM_MESON_TAC[the_same_orbit] ]);;


let node_exceptional_opposite_hypermap = prove ( `! (H:(A)hypermap) (x:A). node_type_exceptional_face H x ==> node_type_exceptional_face (opposite_hypermap H) x`,
GEN_TAC THEN REWRITE_TAC[node_type_exceptional_face;opposite_hypermap]
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap)
THEN REWRITE_TAC[opposite_hypermap] THEN DISCH_TAC THEN MP_TAC (SPEC `H:(A)hypermap` the_SAME_orbit_triangles)
THEN MP_TAC (SPEC `H:(A)hypermap` the_SAME_orbit_quadrilaterals) THEN MP_TAC (SPEC `H:(A)hypermap` the_SAME_orbit_exceptional)
THEN REWRITE_TAC[opposite_hypermap] THEN ABBREV_TAC `D = dart (H:(A)hypermap)` THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`  
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` 
THEN REWRITE_TAC[exceptional_face;node;type_of_node;face]
THEN REWRITE_TAC[set_of_triangles_meeting_node ;set_of_quadrilaterals_meeting_node ;set_of_exceptional_meeting_node]
THEN ASM_REWRITE_TAC[face;node;node_map;face_map;dart] THEN REPEAT STRIP_TAC 
THEN FIRST_X_ASSUM (ASSUME_TAC o (SPEC `x:A`)) THEN FIRST_X_ASSUM (ASSUME_TAC o (SPEC `x:A`)) 
THEN FIRST_X_ASSUM (ASSUME_TAC o (SPEC `x:A`)) 
THEN SUBGOAL_THEN `CARD (orbit_map (f:A->A) (x:A)) >= 5 /\ CARD (orbit_map (n:A->A) x) = 6` ASSUME_TAC
THENL[ASM_MESON_TAC[the_same_orbit];SUBGOAL_THEN ` CARD
          {orbit_map (f:A->A) (y:A) | y | y IN (D:A->bool) /\
                               CARD (orbit_map f y) = 3 /\
                               y IN orbit_map (n:A->A) x} ,
          CARD
          {orbit_map f y | y | y IN D /\
                               CARD (orbit_map f y) = 4 /\
                               y IN orbit_map n x},
          CARD
          {orbit_map f y | y | y IN D /\
                               CARD (orbit_map f y) >= 5 /\
                               y IN orbit_map n x} =
          5,0,1` ASSUME_TAC 
THENL [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ASM_MESON_TAC[] ]]);;


let tame_13_opposite_hypermap = prove ( `!(H:(A)hypermap). tame_13 H ==> tame_13 (opposite_hypermap H)`,
GEN_TAC THEN REWRITE_TAC[tame_13;opposite_hypermap;admissible_weight;total_weight]
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap)
THEN REWRITE_TAC[opposite_hypermap] THEN DISCH_TAC 
THEN MP_TAC (SPEC `H:(A)hypermap` the_SAME_orbit_triangles) THEN MP_TAC (SPEC `H:(A)hypermap` the_SAME_orbit_quadrilaterals)
THEN MP_TAC (SPEC `H:(A)hypermap` the_SAME_orbit_exceptional) THEN MP_TAC (SPEC `H:(A)hypermap` the_SAME_orbit_face)
THEN REWRITE_TAC[opposite_hypermap] THEN ABBREV_TAC `D = dart (H:(A)hypermap)` 
THEN ABBREV_TAC `f = face_map (H:(A)hypermap)` THEN ABBREV_TAC `n = node_map (H:(A)hypermap)`
THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)` THEN ASM_REWRITE_TAC[admissible_weight;face_set;adm_1;adm_2;adm_3;type_of_node]
THEN ASM_REWRITE_TAC[node_map;face_map;set_of_orbits;dart;face;node;set_of_face_meeting_node;set_of_triangles_meeting_node;set_of_quadrilaterals_meeting_node;set_of_exceptional_meeting_node] THEN REPEAT DISCH_TAC THEN FIRST_X_ASSUM ((X_CHOOSE_TAC `w:(A->bool) -> real`))
THEN EXISTS_TAC `w:(A->bool)->real` THEN REPEAT CONJ_TAC
THENL [ASM_MESON_TAC[the_same_orbit]; ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[the_same_set_of_orbits;set_of_orbits] ]);;





let exists_number = prove (`!(p:A->A) (s:A->bool) (x:A) (y:A). FINITE s /\ p permutes s /\  x IN orbit_map (inverse p) y  ==> ? (k:num).(y:A) = ( p POWER (k:num)) (x:A) `,
REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN `?(k':num).(x:A) = (inverse p POWER (k':num)) (y:A)` ASSUME_TAC
THENL [UNDISCH_TAC `(x:A) IN orbit_map (inverse (p:A->A)) (y:A)` THEN REWRITE_TAC[IN_ELIM_THM;orbit_map] THEN MESON_TAC[];
FIRST_X_ASSUM CHOOSE_TAC THEN EXISTS_TAC `k':num` THEN ASM_MESON_TAC[PERMUTES_INVERSE; POWER_INVERSE_o] ]);; 

let MUL_RIGHT_same_orbit = prove ( `!(p:A->A) (s:A->bool) (x:A) (y:A) (k:num). FINITE s /\ p permutes s /\  x = (p POWER k) y  ==> p (y:A) IN orbit_map p (p (x:A)) `,
REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN `p (x:A) = ((p:A->A) POWER (SUC (k:num)))  (y:A)` ASSUME_TAC
THENL [ASM_MESON_TAC[ iterate_map_valuation];
SUBGOAL_THEN `p (x:A) = ((p:A->A) POWER (k:num)) (p (y:A))` ASSUME_TAC
THENL [UNDISCH_TAC ` p (x:A) = ((p:A->A) POWER (SUC (k:num)))  (y:A)` THEN REWRITE_TAC[ADD1;POWER_1;lemma_add_exponent_function];
ASM_MESON_TAC[in_orbit_lemma;orbit_sym] ]]);;

let MUL_RIGHT_not_in_orbit = prove ( `!(p:A->A) (s:A->bool) (z:A) (t:A) . FINITE s /\ p permutes s /\ ~ (z IN orbit_map (inverse p) t) ==> ~ ( p (z:A) IN orbit_map p (p (t:A))) `,
REPEAT GEN_TAC THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN `?(k1:num).p (z:A) = ((p:A->A) POWER (k1:num)) (p (t:A))` ASSUME_TAC
THENL [UNDISCH_TAC `p (z:A) IN orbit_map ((p:A->A)) (p (t:A))` THEN REWRITE_TAC[IN_ELIM_THM;orbit_map] THEN MESON_TAC[];
FIRST_X_ASSUM CHOOSE_TAC THEN SUBGOAL_THEN `(z:A) = ((p:A->A) POWER (k1:num)) (t:A)` ASSUME_TAC
THENL [SUBGOAL_THEN `(p:A->A) (z:A) = (p POWER (k1:num)) (p (t:A))` ASSUME_TAC
THENL [ASM_MESON_TAC[]; SUBGOAL_THEN `(p:A->A) (z:A) = (p POWER (SUC k1:num)) (t:A)` ASSUME_TAC THENL [ASM_MESON_TAC[POWER;o_THM];
ASM_MESON_TAC [ADD1;POWER_1;lemma_add_exponent_function;ADD_SYM;iterate_map_valuation;PERMUTES_INVERSES_o;INJECTIVE_INVERSE_o]]]; 
ASM_MESON_TAC[inverse_same_orbit;in_orbit_lemma] ]]);;


let no_double_joins = prove ( `!(H:(A)hypermap). hypermap_no_double_joins H /\ plain_hypermap H  ==> hypermap_no_double_joins (opposite_hypermap H)`,
GEN_TAC THEN REWRITE_TAC[hypermap_no_double_joins;opposite_hypermap;plain_hypermap;edge;node]
THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma) THEN MP_TAC (SPEC `H:(A)hypermap` opposite_hypermap_plain)
THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap) THEN REWRITE_TAC[opposite_hypermap]   
THEN ABBREV_TAC `D = dart (H:(A)hypermap)` THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`  
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)`
THEN DISCH_TAC THEN ASM_REWRITE_TAC[plain_hypermap;edge_map;node_map;face_map;IN_INTER] THEN REPEAT STRIP_TAC
THEN SUBGOAL_THEN `? (k:num).(z:A) = ((n:A->A) POWER (k:num)) (x:A)` ASSUME_TAC
THENL [ 
      ASM_MESON_TAC [exists_number];
POP_ASSUM CHOOSE_TAC THEN SUBGOAL_THEN `(y:A) = ((f:A->A) o (n:A->A)) (x:A)` ASSUME_TAC
THENL [
      ASM_MESON_TAC[lemma_dart_in_edge;PERMUTES_COMPOSE];
SUBGOAL_THEN `?(l:num).(t:A) = ((n:A->A) POWER (l:num)) (y:A)` ASSUME_TAC
THENL [
      ASM_MESON_TAC[exists_number];
POP_ASSUM CHOOSE_TAC THEN SUBGOAL_THEN `?(h:num).(z:A) = ((n:A->A) POWER (h:num)) (u:A)` ASSUME_TAC
THENL [
      ASM_MESON_TAC[exists_number]; 
POP_ASSUM CHOOSE_TAC THEN SUBGOAL_THEN `?(m:num).(t:A) = ((n:A->A) POWER (m:num)) (v:A)` ASSUME_TAC
THENL [
      ASM_MESON_TAC[exists_number];
POP_ASSUM CHOOSE_TAC THEN SUBGOAL_THEN `(v:A) = ((f:A->A) o (n:A->A)) (u:A)` ASSUME_TAC
THENL [
      ASM_MESON_TAC[lemma_dart_in_edge;PERMUTES_COMPOSE];
ABBREV_TAC `x1 = (n:A->A) (x:A)` THEN POP_ASSUM (ASSUME_TAC o (SYM)) THEN ABBREV_TAC `y1 = (n:A->A) (y:A)`
THEN POP_ASSUM (ASSUME_TAC o (SYM)) THEN ABBREV_TAC `z1 = (n:A->A) (z:A)`THEN POP_ASSUM (ASSUME_TAC o (SYM))
THEN ABBREV_TAC `t1 = (n:A->A) (t:A)` THEN POP_ASSUM (ASSUME_TAC o (SYM)) THEN ABBREV_TAC `u1 = (n:A->A) (u:A)`
THEN POP_ASSUM (ASSUME_TAC o (SYM)) THEN ABBREV_TAC `v1 = (n:A->A) (v:A)` THEN POP_ASSUM (ASSUME_TAC o (SYM))
THEN SUBGOAL_THEN `(x1:A) IN orbit_map (n:A->A) (z1:A)` ASSUME_TAC
THENL [
      ASM_MESON_TAC[MUL_RIGHT_same_orbit];
SUBGOAL_THEN `(y1:A) IN orbit_map (n:A->A) (t1:A)` ASSUME_TAC
THENL [
      ASM_MESON_TAC[MUL_RIGHT_same_orbit];  
SUBGOAL_THEN `(n:A->A) o (f:A->A) = (e:A->A)` ASSUME_TAC
THENL [
      ASM_MESON_TAC[cyclic_maps;INVERSE_UNIQUE_o;o_ASSOC];
SUBGOAL_THEN `(y1:A) IN orbit_map (e:A->A) (x1:A)` ASSUME_TAC
THENL [
      SUBGOAL_THEN `(y1:A) = (e:A->A) (x1:A)` ASSUME_TAC
      THENL [SUBGOAL_THEN `(n:A->A) (y:A) = (n o (f:A->A))  (n (x:A))` ASSUME_TAC
             THENL [ASM_MESON_TAC[LEFT_MULT_MAP;o_THM;o_ASSOC];ASM_MESON_TAC[]];ASM_MESON_TAC[in_orbit_lemma;POWER_1]];
SUBGOAL_THEN `~((x1:A) = (y1:A))` ASSUME_TAC
THENL [
      ASM_CASES_TAC `x1:A = y1:A` THENL [SUBGOAL_THEN `x:A = y:A` ASSUME_TAC THENL [ASM_MESON_TAC[PERMUTES_INVERSES_o;INJECTIVE_INVERSE_o];
  ASM_MESON_TAC[]];FIRST_ASSUM ACCEPT_TAC ]; 
SUBGOAL_THEN `~((z1:A) IN orbit_map (n:A->A) (t1:A))` ASSUME_TAC  
THENL [
      ASM_MESON_TAC[MUL_RIGHT_not_in_orbit];
SUBGOAL_THEN `(u1:A) IN orbit_map (n:A->A) (z1:A)` ASSUME_TAC
THENL [
      ASM_MESON_TAC[MUL_RIGHT_same_orbit];  
SUBGOAL_THEN `(v1:A) IN orbit_map (n:A->A) (t1:A)` ASSUME_TAC
THENL [
      ASM_MESON_TAC[MUL_RIGHT_same_orbit];  
SUBGOAL_THEN `(v1:A) IN orbit_map (e:A->A) (u1:A)` ASSUME_TAC
THENL [
      SUBGOAL_THEN `(v1:A) = (e:A->A) (u1:A)` ASSUME_TAC THENL [SUBGOAL_THEN `(n:A->A) (v:A) = (n o (f:A->A))  (n (u:A))` ASSUME_TAC
      THENL [ASM_MESON_TAC[LEFT_MULT_MAP;o_THM;o_ASSOC];ASM_MESON_TAC[]]; ASM_MESON_TAC[in_orbit_lemma;POWER_1]];
SUBGOAL_THEN `~((v1:A) = (u1:A))` ASSUME_TAC 
THENL [
      ASM_CASES_TAC `v1:A = u1:A` THENL [SUBGOAL_THEN `u:A = v:A` ASSUME_TAC THENL [ASM_MESON_TAC[PERMUTES_INVERSES_o;INJECTIVE_INVERSE_o];
ASM_MESON_TAC[]];FIRST_ASSUM ACCEPT_TAC ];  
SUBGOAL_THEN ` (x1:A) IN orbit_map (e:A->A) (u1:A)` ASSUME_TAC
THENL [
      FIRST_X_ASSUM (ASSUME_TAC o SPECL [`x1:A`;`y1:A`; `z1:A`;`t1:A`;`u1:A`;`v1:A`]) THEN ASM_MESON_TAC[];
ASM_CASES_TAC `x:A = u:A` 
THENL [
      ASM_REWRITE_TAC[orbit_reflect];
SUBGOAL_THEN `~((x1:A) = (u1:A))` ASSUME_TAC
THENL [
      ASM_CASES_TAC `x1:A = u1:A` THENL [SUBGOAL_THEN `x:A = u:A` ASSUME_TAC THENL [ASM_MESON_TAC[PERMUTES_INVERSES_o;INJECTIVE_INVERSE_o];
ASM_MESON_TAC[]];FIRST_ASSUM ACCEPT_TAC]; 
SUBGOAL_THEN `x1:A = (e:A->A) (u1:A)` ASSUME_TAC
THENL [
      ASM_MESON_TAC[ lemma_dart_in_edge];
SUBGOAL_THEN `(n:A->A) (x:A) = (n o (f:A->A)) (n (u:A))` ASSUME_TAC
THENL [
      ASM_MESON_TAC[];
SUBGOAL_THEN `x:A = ((f:A->A) o (n:A->A)) (u:A)` ASSUME_TAC
THENL [
      ASM_MESON_TAC[o_THM;o_ASSOC;PERMUTES_INVERSES_o;INJECTIVE_INVERSE_o];
ASM_MESON_TAC[in_orbit_lemma] ]]]]]]]]]]]]]]]]]]]]]] );;


let tame_opposite_hypermap = prove ( `!(H:(A)hypermap). tame_hypermap H ==> tame_hypermap (opposite_hypermap H)`,
GEN_TAC THEN REWRITE_TAC [tame_hypermap;tame_1; tame_2;tame_3; tame_4 ; tame_5 ; tame_12o ] 
THEN ASM_MESON_TAC [opposite_hypermap_plain;opposite_hypermap_simple;opposite_hypermap_connected;opposite_nondegenerate;opposite_planar;CARD_faces1;CARD_in_face;CARD_nodes;CARD_in_node;thm_no_loops; node_opposite_exceptional_face;node_exceptional_opposite_hypermap; tame_13_opposite_hypermap;no_double_joins] );;

let opposite_opposite_hypermap = prove ( `!(H:(A)hypermap). opposite_hypermap (opposite_hypermap H) = hypermap (dart H,edge_map H,node_map H,face_map H)`,
GEN_TAC THEN REWRITE_TAC[opposite_hypermap] THEN MP_TAC (SPEC `H:(A)hypermap` hypermap_lemma)
THEN MP_TAC (SPEC `H:(A)hypermap` tuple_opposite_hypermap) THEN REWRITE_TAC[opposite_hypermap] 
THEN ABBREV_TAC `D = dart (H:(A)hypermap)` THEN ABBREV_TAC `f = face_map (H:(A)hypermap)`  
THEN ABBREV_TAC `n = node_map (H:(A)hypermap)` THEN ABBREV_TAC `e = edge_map (H:(A)hypermap)`
THEN STRIP_TAC THEN ASM_REWRITE_TAC[node_map;dart;face_map] THEN REPEAT STRIP_TAC
THEN SUBGOAL_THEN `inverse (inverse (n:A->A)) = n` ASSUME_TAC
THENL [
      ASM_MESON_TAC[PERMUTES_INVERSE_INVERSE];
SUBGOAL_THEN `inverse (inverse (f:A->A)) = f` ASSUME_TAC
THENL [
      ASM_MESON_TAC[PERMUTES_INVERSE_INVERSE];
SUBGOAL_THEN `inverse (f:A->A) =  (e:A->A) o (n:A->A)` ASSUME_TAC
THENL [
      ASM_MESON_TAC[cyclic_maps;I_O_ID;INVERSE_UNIQUE_o;o_ASSOC];
SUBGOAL_THEN `inverse (f:A->A) o inverse (n:A->A) = e` ASSUME_TAC
THENL [
      ASM_MESON_TAC[RIGHT_MULT_MAP;PERMUTES_INVERSES_o;o_ASSOC;I_O_ID];
ASM_REWRITE_TAC[] ]]]]);;


let INVERSE_tame_opposite_hypermap = prove ( `! (H:(A)hypermap). tame_hypermap  (opposite_hypermap H) ==> tame_hypermap H`,
GEN_TAC THEN ASSUME_TAC tame_opposite_hypermap THEN FIRST_X_ASSUM (ASSUME_TAC o (SPEC `opposite_hypermap (H:(A)hypermap)`))
THEN UNDISCH_TAC `tame_hypermap (opposite_hypermap H)
      ==> tame_hypermap (opposite_hypermap (opposite_hypermap (H:(A)hypermap)))`
THEN REWRITE_TAC[opposite_opposite_hypermap]
THEN REWRITE_TAC[dart;edge_map;face_map;node_map;hypermap_tybij] );;

let PPHEUFG = prove (`!(H:(A)hypermap). tame_hypermap H <=> tame_hypermap (opposite_hypermap H)`,
MESON_TAC[tame_opposite_hypermap;INVERSE_tame_opposite_hypermap]);;







