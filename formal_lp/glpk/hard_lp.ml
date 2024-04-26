(* ========================================================================== *)
(* FLYSPECK - CODE FORMALIZATION                                              *)
(*                                                                            *)
(* Program: Linear Programs                                                   *)
(* Author: Thomas C. Hales                                                    *)
(* Date: 2010-08-01                                                           *)
(* ========================================================================== *)


(*
The purpose of this file is to treat the 12 hard tame hypermaps that
are not treated in lpproc.ml.
*)

needs "../formal_lp/glpk/sphere.ml";;

module Hard_lp = struct 

(* code for the hard cases... *)

let hardidref = ref Lpproc.hardid;;

open Str;;
open List;;
open Glpk_link;;
open Lpproc;;

let sqrt = Stdlib.sqrt;;
let dih_y = Sphere_math.dih_y;;

(*
The purpose of this first section is to build up tables of what the
LP solution gives as the dihedral angles 
versus the floating point calculation of dihedral angles.

The idea is that branching should occur where the discrepancy is the biggest.
*)

(* build up hashtables of all the variables assignments from the glpk_outfile *)

let new_tables () = (Hashtbl.create 13,Hashtbl.create 70,Hashtbl.create 70);;

let tables bb = match bb.diagnostic with
    Hash_tables (a,b,c) -> (a,b,c);;

let ynhash bb= (fun (a,_,_) -> a) (tables bb);;
let yehash bb = (fun (_,a,_) -> a) (tables bb);;
let azimhash bb = (fun (_,_,a) -> a) (tables bb);;

let yn bb i = Hashtbl.find (ynhash bb) i;;
let ye bb (i,j) = Hashtbl.find (yehash bb) (i,j);;
let azim bb (i,j) = Hashtbl.find (azimhash bb) (i,j);;

(*
There is state involved here.  This code is rather fragile.
The glpk_outfile gets overwritten the next time solve is called.
So we want to generate the hash tables right after solve is called.
*)

(* this renews the glpk_outfile *)
let resolve bb = solve_branch_verbose (fun t->t) bb;;

let init_hash_verified_glpk_outfile glpk_outfile bb = 
  let _ = (bb.diagnostic <- Hash_tables (new_tables())) in
  let _ = Hashtbl.clear (ynhash bb) in
  let _ = Hashtbl.clear (yehash bb) in
  let _ = Hashtbl.clear (azimhash bb) in
  let com = sprintf "cat %s | grep -v ':'  | grep '=' | tr '[\[\]=,]' ' ' | sed 's/.val//' | sed 's/\( [0-9]*\)$/\1.0/g'" glpk_outfile in
  let is = int_of_string in
  let fs = float_of_string in
  let (ic,oc) = Unix.open_process(com) in
  let _  = close_out oc in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process(ic,oc) in
  let split_sp=  Str.split (regexp " +") in
  let inpa = map split_sp inp in
  let ynproc [a;b;c] = Hashtbl.add (ynhash bb) (is b) (fs c) in
  let yeproc [a;b;c;d] = Hashtbl.add (yehash bb) ( (is b), (is c)) (fs d) in
  let azimproc [a;b;c;d] = Hashtbl.add (azimhash bb) ( (is b), (is c)) (fs d) in
  let proc1 xs = 
    begin
      let a = hd xs in
      if (a = "yn") then ynproc xs
      else if (a = "ye") then yeproc xs
      else if (a = "azim") then azimproc xs
     end in
  let _ = try (map proc1 inpa) with Failure _ -> failwith "init_has_v" in ();;

let init_hash bb = 
  match bb.diagnostic with
    | File (glpk_outfile,dig) ->  if not(dig = Digest.file glpk_outfile) 
      then (bb.diagnostic <- No_data; failwith "init_hash:stale") 
      else init_hash_verified_glpk_outfile glpk_outfile bb
    | _ -> ();;

(* look at edge lengths and azimuth angles of a triangle *)
let int_of_face xs bb = wheremod (faces bb) xs;;

(* get_azim_table dih_y [2;4;3] bb;; *)

let get_azim_dart_diff f xs bb = 
   let [y1;y2;y3] = map (yn bb) xs in
   let [y6;y4;y5] = map (fun i -> (ye bb (i,int_of_face xs bb))) xs in
   let a1 = azim bb (hd xs, int_of_face xs bb) in
   let b1 = f y1 y2 y3 y4 y5 y6 in
   abs_float (a1 -. b1);;
(* get_azim_dart_diff dih_y [2;4;3] bb;;  *)

(* first entry is the triangle with the biggest azim error. *)
let sorted_azim_diff p bb = 
  let ys = p bb in 
  let u = map (fun t->  (get_azim_dart_diff dih_y t bb  ,t))  ys in
  let v = List.sort (fun a b -> - Stdlib.compare (fst a) (fst b)) u in
   v;;
(* sorted_azim_diff darts_of_std_tri bb;;   *)

(* if we always do branching on the worst triangle, we quickly run out of
    possibilities because we can get stuck on a single triangle.  We need a
    heuristic that moves emphasis away from triangles where extensive branching
    has already been done.  Here is my heuristic to do so.   Many different
    strategies are possible.  This works sufficiently well in practice.  *)

let heuristic_weight d bb = 
  if not(mem d (rotation (bb.std3_small @ bb.std3_big))) then 1.0 else
  if not(subset d (bb.node_200_218 @ bb.node_218_252)) then 0.7 else
  if not(subset d (bb.node_200_218 @ bb.node_218_236 @ bb.node_236_252)) then 0.49 else
  if not(subset (rotation [d]) (bb.d_edge_200_225 @ bb.d_edge_225_252 @ map (rotateL 1) bb.apex_flat)) then 0.3
  else 0.0;;

(* first entry is the triangle with the biggest azim weighted error. *)

let sorted_azim_weighted_diff p bb = 
  let ys = p bb in 
  let u = map (fun t->  ((heuristic_weight t bb *. get_azim_dart_diff dih_y t bb)  ,t))  ys in
  let v = List.sort (fun a b -> - Stdlib.compare (fst a) (fst b)) u in
   v;;


(* ------------------------ *)
(* HINTS *)

(* add_hints is called right after the LP is solved and the lpvalue set.  
    The glpk_outfile has been initialized. *)

let darts_of_std_tri bb =
  rotation(filter (fun t -> length t = 3) bb.std_faces_not_super);;

let darts_of_std_tri_and_flats bb =
  rotation(filter (fun t -> length t = 3) (bb.std_faces_not_super @ bb.apex_flat));;

let highish bb = subtract bb.node_218_252 (bb.node_218_236 @ bb.node_236_252);;

let face_of_dart fc bb = 
  let xss = map triples (faces bb) in
  nth (find (fun t -> mem fc t) xss) 0;;

let add_hints_force bb = 
  try(
    let _ = init_hash bb in
  let dart = snd(hd(sorted_azim_weighted_diff darts_of_std_tri bb)) in 
  let f = face_of_dart dart bb in
  if not(mem f (bb.std3_big @ bb.std3_small)) then bb.hints <-  [Triangle_split f] else
  let f1 = subtract f  (bb.node_200_218 @ bb.node_218_252) in
  if not(f1 = []) then bb.hints <- [High_low (hd f1)] else 
    let f2 = intersect (highish bb) f in
  if not(f2 = []) then  bb.hints <- [High_low (hd f2)] else
    let d1 = subtract (rotation [dart]) (bb.d_edge_200_225 @ bb.d_edge_225_252) in
  if not (d1 = []) then bb.hints <- [Edge_split (hd d1)] else ()
  ) with | Failure s -> failwith (s^"in add_hints")
    | Not_found -> failwith "Not_found add_hints_force";;


let add_hints_force_include_flat bb = 
  try(
    let _ = init_hash bb in
    let dart = snd(hd(sorted_azim_weighted_diff darts_of_std_tri_and_flats bb)) in 
    let f = face_of_dart dart bb in
      if (mem f (rotation bb.std_faces_not_super)) then add_hints_force bb else
	let f1 = subtract f  (bb.node_200_218 @ bb.node_218_252) in
	  if not(f1 = []) then bb.hints <- [High_low (hd f1)] else 
	    let f2 = intersect (highish bb) f in
	      if not(f2 = []) then  bb.hints <- [High_low (hd f2)] else 
		add_hints_force bb
  ) with | Failure s -> failwith ( s^" in add_hints_force_include_flat")
    | Not_found -> failwith ( " Not_found in add_hints_force_include_flat");;


let add_hints_include_flat bb = 
  if not(is_feas bb) then () else
  if not(bb.hints = []) then () else
    add_hints_force_include_flat bb;;

(* ------------------------ *)

let is_none bb = match bb.lpvalue with (* for debugging *)
  | Lp_value _ -> false
  | _ -> true;;


let calc_max bbs = fold_right 
  (fun bb x -> match bb.lpvalue with
    |Lp_value y -> max x y
    |_  -> x)   
  bbs 0.0 ;;

let find_max bbs = 
  let r = Lp_value (calc_max bbs) in
    find (fun bb -> r = bb.lpvalue) bbs;;

let findid s  = find (fun t -> s = t.hypermap_id);;

let findid_list s = filter (fun t -> s = t.hypermap_id);;


(*
We are proving the bound L(V) <= 12.  When there are 13 nodes,
this is automatic when the nodes excess heights (|v|-2) add up to at least 0.52.
Fail if the bb already satisfies L(V) <= 12.
*)

let node_list bb = 0 -- (card_node bb - 1);;

let set_node_numerics bb = 
  if not(card_node bb = 13) then bb else
  let n_high = length bb.node_236_252 in
  let n_mid = length bb.node_218_236 in
  let n_highish = length (highish bb) in
  if (n_high =0 )  && (n_mid +n_highish < 2) then bb else
  let _ = (n_mid * 18 + n_highish * 18 + n_high *36 <= 52) || failwith "set_node_numerics" in
  let node_new_low = subtract (node_list bb) (unions [bb.node_200_218 ;bb.node_218_236; bb.node_236_252;bb.node_218_252]) in
  let vfields_low = map (fun t -> ("200_218",t)) node_new_low in
  let vfields_mid = map(fun t->("218_236",t)) (highish bb) in
  let vfields = vfields_low @ vfields_mid in
    if vfields = [] then bb else     modify_bb bb false [] vfields;;

(*
let t1 = modify_bb  (pent_bb) false [] ["236_252",5];;
set_node_numerics t1;;
let t1 = modify_bb  (pent_bb) false [] [("236_252",5);("218_236",3)];;
can set_node_numerics t1;;
let t1 = modify_bb  (pent_bb) false [] [("218_236",5);("218_236",3)];;
set_node_numerics t1;;
let t1 = modify_bb  (pent_bb) false [] [("218_236",5);("218_252",3)];;
set_node_numerics t1;;
*)

let opposite_edge [i;j;k] bb =
  let f = find (fun t -> (nth t 0 = j) && (nth t 1 = i)) (rotation (faces bb)) in
   [j;i;nth f 2];;

(*
if a face is small the three edges lie in the range [2,2.25].
if an edge is in the range (2.25,2.52], then the face is big.
A directed edge is in the same category as the oppositely directed edge.
*)

let set_face_numerics bb = 
  let opp xs = nub (xs @ map (C opposite_edge bb) xs) in
  let edge_of_small = opp (rotation bb.std3_small) in
  let short_edge = opp bb.d_edge_200_225 in
  let long_edge = opp bb.d_edge_225_252 in
  let _ =  (intersect edge_of_small long_edge = []) || failwith "set_face_numerics" in
  let shortadds =  subtract (edge_of_small @ short_edge) bb.d_edge_200_225 in
  let shortfields = (map (fun t-> ("e_200_225",t)) shortadds) in
  let longadds =  subtract long_edge bb.d_edge_225_252 in
  let longfields = (map (fun t-> ("e_225_252",t)) longadds) in
  let r = filter (fun t -> mem t (std_faces bb) && (length t = 3) )
          (nub (map (C face_of_dart bb) long_edge)) in
  let _ = (intersect (rotation bb.std3_small) r =[]) || failwith "set_face_numerics" in
  let bigfields = map (fun t -> ("bt",t)) (subtract r bb.std3_big) in
  let fields = shortfields @ longfields @ bigfields in
    if fields=[] then bb else     modify_bb bb false fields [];;


(*
let t1 = modify_bb pent_bb false [("st",[9;6;10]);("e_225_252",[7;8;12])] [];;
set_face_numerics t1;;    
let t1 = modify_bb pent_bb false ["st",[8;2;1]] [];;
set_face_numerics t1;;
let t1 = modify_bb pent_bb false ["e_225_252",[7;12;11]] [];;
set_face_numerics t1;;
*)

(*
Hints are given as a list.  However, I never ended up using more
than a single hint at a time.  It could be restructured as 
Some _ | None.
*)

(* ------------------------ *)
(* switch and selection functions *)

let clear_hint bb = 
  if (bb.hints = []) then () else (bb.hints <- tl bb.hints);;

let switch_std3 d bb = 
  let c = face_of_dart d bb in 
  [modify_bb bb false ["bt",c] [];modify_bb bb false ["st",c] []];;

let switch_edge d bb = 
      [modify_bb bb false ["e_225_252",d] [];modify_bb bb false ["e_200_225",d] []];; 

let switch_node bb i = 
  if (mem i (highish bb)) then 
  [modify_bb bb false [] ["218_236",i];modify_bb bb false [] ["236_252",i]] else
    let settable = subtract (node_list bb ) (bb.node_200_218 @ bb.node_218_236 @ bb.node_236_252) in
  if not(mem i settable) then failwith "switch_node" else
  [modify_bb bb false [] ["218_252",i];modify_bb bb false [] ["200_218",i]];;

let follow_hint bb = 
  let _ =assert(not(bb.hints = [])) in
  let hint = hd (bb.hints) in
(*  let _ = clear_hint bb in *)
  let sbb = match hint with
  | Triangle_split d -> switch_std3 d bb
  | High_low i -> switch_node bb i 
  | Edge_split d -> switch_edge d bb in
  let _ = map clear_hint sbb in sbb;;

let filter_feas_hint_include_flat bbs = filter_feas_f add_hints_include_flat bbs;;

let switch_hint bb = 
   if (length bb.std_faces_not_super > 0) && 
      (length (hd bb.std_faces_not_super) > 3) then switch_face bb 
   else if not(bb.hints = []) then follow_hint bb else [bb];;

(* For debugging purposes, when we interrupt a calculation *)

let onepass_backup = ref [];;  

let sortbb bbs = 
  let eval bb = (match bb.lpvalue with Lp_value r -> r | _ -> 0.0) in
  let v = List.sort (fun a b -> - Stdlib.compare (eval a) (eval b)) bbs in
   v;;



(* One iteration of the main loop *)

let onepass_hint_include_flat = function 
  [] -> []
  | bb::bbss as bbs -> 
  let _ = onepass_backup := bbs in
  let brs =  switch_hint bb in
  let brs1 = map set_face_numerics brs in
  let brs2 = map set_node_numerics brs1 in
  let _ = echo bbs in
    sortbb ((filter_feas_hint_include_flat brs2) @ bbss);;


(* The main loop *)

let rec allpass_hint_include_flat count bbs = 
   if  count <= 0 then bbs else allpass_hint_include_flat (count - 1) 
   (onepass_hint_include_flat bbs);;

let hard_string_rep() = 
   List.find_all (fun (h,_,_) -> mem h !hardidref) 
   (Archive_all.tame_list);;

let resolve_with_hints_include_flat t = 
  let u = resolve t in 
  let _ = add_hints_force_include_flat u in
    u;;

let hard_bb() =  
  let r = map mk_order_bb (hard_string_rep()) in
  map resolve_with_hints_include_flat r;;

let hard i = List.nth (hard_bb()) i;;

(* if successful, all lists will be empty.  This takes several hours
    to run on my laptop.  *)

let execute() = 
  let _ = Lpproc.make_model() in 
  let _ = resetc() in
  map (fun t-> allpass_hint_include_flat 20000 [t]) (hard_bb());;

end;;
