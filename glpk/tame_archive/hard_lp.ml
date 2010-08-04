(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(*                                                                            *)
(* Chapter: Linear Programs                                                               *)
(* Author: Thomas C. Hales                                                    *)
(* Date: 2010-08-01                                                           *)
(* ========================================================================== *)


module Hard_lp = struct 

(* code for the hard cases... *)

let glpk_dir =  "/Users/thomashales/Desktop/googlecode/flyspeck/glpk/";;
(* 
#use "glpk_link.ml";;
#use "tame_archive/lpproc.ml";;
#use "sphere.ml";;
*)



open Str;;
open List;;
open Glpk_link;;
open Lpproc;;

let sqrt = Pervasives.sqrt;;
let dih_y = Sphere_math.dih_y;;

(* Generate graphics files of a branchnbound, save gif as a /tmp file.  *)

let mk_gif bb = (Sys.chdir 
 "/Users/thomashales/Desktop/googlecode/flyspeck/graph_generator/classes"; 
 Sys.command 
    ("java render/Gendot \""^bb.string_rep ^
      "\" | neato -s -n -Tgif -o "^ 
    (Filename.temp_file ("render"^bb.hypermap_id^"_") (".gif"))));;

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
  let com = sprintf "cat %s | grep -v ':'  | grep '=' | tr '[\[\]=,]' ' ' | sed 's/\( [0-9]*\)$/\1.0/g'" glpk_outfile in
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

let get_azim_table xs bb = 
   let [y1;y2;y3] = map (yn bb) xs in
   let [y6;y4;y5] = map (fun i -> ye bb ( i, int_of_face xs bb)) xs in
   let [a1;a2;a3] = map (fun i -> azim bb (i, int_of_face xs bb)) xs in
   let b1 = dih_y y1 y2 y3 y4 y5 y6 in
   let b2 = dih_y y2 y3 y1 y5 y6 y4 in
   let b3 = dih_y y3 y1 y2 y6 y4 y5 in
   (y1,y2,y3,y4,y5,y6,("dih_lp",a1,"dih_y",b1,a1-. b1),("dih2_lp",a2,"dih2_y",b2,a2-. b2),("dih3_lp",a3,"dih3_y",b3,a3 -. b3),"soldiff",a1+. a2 +. a3 -.( b1 +. b2 +. b3));;

let testval f xs bb = 
  let (y1,y2,y3,y4,y5,y6,_,_,_,_,_) = get_azim_table xs bb in
  f y1 y2 y3 y4 y5 y6;;

let testvalsym d  = testval (fun y1 y2 y3 y4 y5 y6 -> d y1 y3 y2 y4 y6 y5);;

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
  let v = List.sort (fun a b -> - compare (fst a) (fst b)) u in
   v;;
(* sorted_azim_diff darts_of_std_tri bb;;   *)

(* if we always do branching on the worst triangle, we quickly run out of
    possibilities because we can get stuck on a single triangle.  We need a
    heuristic that moves emphasis away from triangles where extensive branching
    has already been done.  Here is my heuristic to do so.   Many different
    strategies are possible.   *)

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
  let v = List.sort (fun a b -> - compare (fst a) (fst b)) u in
   v;;
  get_azim_dart_diff;;

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
  ) with Failure _ -> failwith "add_hints";;

let add_hints_force_include_flat bb = 
  try(
    let _ = init_hash bb in
  let dart = snd(hd(sorted_azim_weighted_diff darts_of_std_tri_and_flats bb)) in 
  let f = face_of_dart dart bb in
  if (mem f (rotation bb.std_faces_not_super)) then add_hints_force bb else
  let f1 = subtract f  (bb.node_200_218 @ bb.node_218_252) in
  if not(f1 = []) then bb.hints <- [High_low (hd f1)] else 
    let f2 = intersect (highish bb) f in
  if not(f2 = []) then  bb.hints <- [High_low (hd f2)] else ()
  ) with Failure _ -> failwith "add_hints_flat";;

let add_hints bb = 
  if not(is_feas bb) then () else
  if not(bb.hints = []) then () else
    add_hints_force bb;;

let add_hints_include_flat bb = 
  if not(is_feas bb) then () else
  if not(bb.hints = []) then () else
    add_hints_force_include_flat bb;;

(* ------------------------ *)

let is_none bb = match bb.lpvalue with (* for debugging *)
    None -> true
  | Some _ -> false;;

let calc_max bbs = fold_right 
  (fun bb x -> match bb.lpvalue with
     |None -> x
     |Some y -> max x y) bbs 0.0;;

let find_max bbs = 
  let r = Some (calc_max bbs) in
    find (fun bb -> r = bb.lpvalue) bbs;;

let findid s  = find (fun t -> s = t.hypermap_id);;

let findid_list s = filter (fun t -> s = t.hypermap_id);;

(*   *)

let check_basic_format bb =
    (subset bb.std3_small  (rotation bb.std_faces_not_super)) &
    (subset bb.std3_big (rotation bb.std_faces_not_super)) &
    (intersect (rotation bb.std3_small) (rotation bb.std3_big) = []) &
    (subset bb.node_218_236 bb.node_218_252) &
    (subset bb.node_236_252 bb.node_218_252);;

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
  if (n_high =0 )  & (n_mid +n_highish < 2) then bb else
  let _ = (n_mid * 18 + n_highish * 18 + n_high *36 <= 52) or failwith "set_node_numerics" in
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
  let f = find (fun t -> (nth t 0 = j) & (nth t 1 = i)) (rotation (faces bb)) in
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
  let _ =  (intersect edge_of_small long_edge = []) or failwith "set_face_numerics" in
  let shortadds =  subtract (edge_of_small @ short_edge) bb.d_edge_200_225 in
  let shortfields = (map (fun t-> ("e_200_225",t)) shortadds) in
  let longadds =  subtract long_edge bb.d_edge_225_252 in
  let longfields = (map (fun t-> ("e_225_252",t)) longadds) in
  let r = filter (fun t -> mem t (std_faces bb) & (length t = 3) )
          (nub (map (C face_of_dart bb) long_edge)) in
  let _ = (intersect (rotation bb.std3_small) r =[]) or failwith "set_face_numerics" in
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

let filter_feas_hint bbs = filter_feas_f add_hints bbs;;

let filter_feas_hint_include_flat bbs = filter_feas_f add_hints_include_flat bbs;;

let switch_hint bb = 
   if (length bb.std_faces_not_super > 0) & 
      (length (hd bb.std_faces_not_super) > 3) then switch_face bb 
   else if not(bb.hints = []) then follow_hint bb else [bb];;

let onepass_backup = ref [];;  (* in case we interrupt a calculation *)

let sortbb bbs = 
  let eval bb = (match bb.lpvalue with None -> 0.0 | Some r -> r) in
  let v = List.sort (fun a b -> - compare (eval a) (eval b)) bbs in
   v;;

let onepass_hint = function 
  [] -> []
  | bb::bbss as bbs -> 
  let _ = onepass_backup := bbs in
  let brs =  switch_hint bb in
  let brs1 = map set_face_numerics brs in
  let brs2 = map set_node_numerics brs1 in
  let _ = echo bbs in
    sortbb ((filter_feas_hint brs2) @ bbss);;

let rec allpass_hint count bbs = 
   if  count <= 0 then bbs else allpass_hint (count - 1) (onepass_hint bbs);;

let onepass_hint_include_flat = function 
  [] -> []
  | bb::bbss as bbs -> 
  let _ = onepass_backup := bbs in
  let brs =  switch_hint bb in
  let brs1 = map set_face_numerics brs in
  let brs2 = map set_node_numerics brs1 in
  let _ = echo bbs in
    sortbb ((filter_feas_hint_include_flat brs2) @ bbss);;

let rec allpass_hint_include_flat count bbs = 
   if  count <= 0 then bbs else allpass_hint_include_flat (count - 1) 
   (onepass_hint_include_flat bbs);;

(* for debugging, we don't want overly long lists. Pick out random elts. *)

let random_elt xs = 
  let i = Random.int (length xs) in
  let r = nth xs i in
   r, (subtract xs [r]);;

let rec random_elts n xs =
  if n=0 then ([],xs) else 
    let (a,b) = random_elts (n-1)  xs in
    let (r,s) = random_elt b in (r::a,s);;

let get_highest n bbs =
  let eval bb = (match bb.lpvalue with None -> 0.0 | Some r -> r) in
  (chop_list n (sort (fun b1 b2 -> eval b1 > eval b2) bbs));;

let prune_results n bbs = 
   if length bbs <= 2*n then bbs else
     let (b1,b2) = get_highest n bbs in
     b1 @ fst (random_elts n b2);;
     
let rec allpass_prune_hint prune count bbs = 
   if  count <= 0 then bbs else allpass_prune_hint prune (count - 1) (prune_results prune (onepass_hint bbs));;


end;;
