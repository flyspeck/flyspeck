(* tests of the final cases... *)

#directory "/Users/thomashales/Desktop/googlecode/flyspeck/glpk/";;
#use "glpk_link.ml";;
#use "tame_archive/lpproc.ml";;

#use "sphere.ml";;

open Str;;
open List;;
open Glpk_link;;
open Lpproc;;

let sqrt = Pervasives.sqrt;;
let dih_y = Sphere_math.dih_y;;
(* let dumpfile = Filename.temp_file "test_lp_dump_" ".out";; *)

(* Generate graphics files of a branchnbound, save gif as a /tmp file.  *)

let mk_gif bb = (Sys.chdir 
 "/Users/thomashales/Desktop/googlecode/flyspeck/graph_generator/classes"; 
 Sys.command 
    ("java render/Gendot \""^bb.string_rep ^
      "\" | neato -s -n -Tgif -o "^ 
    (Filename.temp_file ("render"^bb.hypermap_id^"_") (".gif"))));;

(* build up hashtables of all the variables assignments from the dumpfile *)
let ynhash= Hashtbl.create 13;;
let yehash = Hashtbl.create 70;;
let azimhash = Hashtbl.create 70;;
let yn i = Hashtbl.find ynhash i;;
let ye (i,j) = Hashtbl.find yehash (i,j);;
let azim(i,j) = Hashtbl.find azimhash (i,j);;

(*
There is state involved here.  This code is rather fragile.
The dumpfile gets overwritten the next time solve is called.
First initialize the dumpfile, 
then call init_hash to populate the hash tables.
*)

let init_dumpfile dumpfile bb = solve_branch_f model dumpfile "lnsum" ampl_of_bb bb;;

let init_hash dumpfile = 
  let com = sprintf "cat %s | grep -v ':'  | grep '=' | tr '[\[\]=,]' ' ' | sed 's/\( [0-9]*\)$/\1.0/g'" dumpfile in
  let is = int_of_string in
  let fs = float_of_string in
  let (ic,oc) = Unix.open_process(com) in
  let _  = close_out oc in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process(ic,oc) in
  let split_sp=  Str.split (regexp " +") in
  let inpa = map split_sp inp in
  let _ = Hashtbl.clear ynhash in
  let _ = Hashtbl.clear yehash in
  let _ = Hashtbl.clear azimhash in
  let ynproc [a;b;c] = Hashtbl.add ynhash (is b) (fs c) in
  let yeproc [a;b;c;d] = Hashtbl.add yehash ( (is b), (is c)) (fs d) in
  let azimproc [a;b;c;d] = Hashtbl.add azimhash ( (is b), (is c)) (fs d) in
  let proc1 xs = 
    let a = hd xs in
      if (a = "yn") then ynproc xs
      else if (a = "ye") then yeproc xs
      else if (a = "azim") then azimproc xs in
  let _ = map proc1 inpa in ();;
(* init_hash ();; *)

(* for debugging: reading optimal variables values from the dumpfile *)

let get_dumpvar dumpfile s = (* read variables from dumpfile *)
  let com = sprintf "grep '%s' %s | sed 's/^.*= //'  " s dumpfile in
  let (ic,oc) = Unix.open_process(com) in
  let _ = close_out oc in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process(ic,oc) in
  inp;;
(* get_dumpvar "yn.0.*=";; *)


let float_of_dump s = float_of_string (hd s);;
let get_float dumpfile s = float_of_dump(get_dumpvar dumpfile s);;
let int_of_face xs bb = wheremod (faces bb) xs;;

(*
let get_sol xs bb = get_float (sprintf "sol.%d.*=" (int_of_face xs bb));;
(* get_sol [12;7;8] bb;; *)

let get_tau xs bb = get_float (sprintf "tau.%d.*=" (int_of_face xs bb));;
(* get_tau [12;7;8] bb;; *)
*)

(* for debugging: look at edge lengths and azimuth angles of a triangle *)

let get_azim_table f xs bb = 
   let [y1;y2;y3] = map yn xs in
   let [y6;y4;y5] = map (fun i -> ye ( i, int_of_face xs bb)) xs in
   let [a1;a2;a3] = map (fun i -> azim (i, int_of_face xs bb)) xs in
   let b1 = f y1 y2 y3 y4 y5 y6 in
   let b2 = f y2 y3 y1 y5 y6 y4 in
   let b3 = f y3 y1 y2 y6 y4 y5 in
   (y1,y2,y3,y4,y5,y6,(a1,b1,a1-. b1),(a2,b2,a2-. b2),(a3,b3,a3 -. b3),a1+. a2 +. a3 -.( b1 +. b2 +. b3));;

(* get_azim_table dih_y [2;4;3] bb;; *)

let get_azim_diff f xs bb = 
   let [y1;y2;y3] = map yn xs in
   let [y6;y4;y5] = map (fun i -> ye (i,int_of_face xs bb)) xs in
   let a1 = azim (hd xs, int_of_face xs bb) in
   let b1 = f y1 y2 y3 y4 y5 y6 in
   abs_float (a1 -. b1);;
(* get_azim_diff dih_y [2;4;3] bb;;  *)

(* experimental: first entry is the triangle with the biggest azim error. *)
let sorted_azim_diff dumpfile p bb = 
  let _ = init_hash dumpfile in
  let ys = p bb in 
  let u = map (fun t->  (get_azim_diff dih_y t bb  ,t))  ys in
  let v = List.sort (fun a b -> - compare (fst a) (fst b)) u in
   v;;
(* sorted_azim_diff get_tri bb;;   *)

(* ------------------------ *)
(* HINTS *)

(* add_hints is called right after the LP is solved and the lpvalue set.  
    The dumpfile has been initialized. *)

let darts_of_std_tri bb =
  rotation(filter (fun t -> length t = 3) bb.std_faces_not_super);;

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

let findall s = filter (fun t -> s = t.hypermap_id);;

(*   *)

let check_basic_format bb =
    (subset bb.std3_small  (rotation bb.std_faces_not_super)) &
    (subset bb.std3_big (rotation bb.std_faces_not_super)) &
    (intersect (rotation bb.std3_small) (rotation bb.std3_big) = []) &
    (subset bb.node_218_236 bb.node_218_252) &
    (subset bb.node_236_252 bb.node_218_252);;


let face_of_dart fc bb =   (* dart as rotated list of any length *)
  let xss = map (fun t-> rotation [t]) (faces bb) in
  nth (find (fun t -> mem fc t) xss) 0;;

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
  if (n_high =0 )  & (n_mid < 2) then bb else
  let _ = (n_high =0) or (n_mid = 0) or failwith "set_node_numerics" in
  let _ = (n_high <=1) or  failwith "set_node_numerics" in  
  let _ = (n_mid <= 2) or failwith "set_node_numerics" in (* 3 * 0.18 > 0.52, etc. *)
  let node_new_low = subtract (node_list bb) (unions [bb.node_200_218 ;bb.node_218_236; bb.node_236_252]) in
  let vfields = map (fun t -> ("200_218",t)) node_new_low in
    modify_bb bb false [] vfields;;

(*
let t1 = modify_bb  (pent_bb) false [] ["236_252",5];;
set_node_numerics t1;;
let t1 = modify_bb  (pent_bb) false [] [("236_252",5);("218_236",3)];;
can set_node_numerics t1;;
let t1 = modify_bb  (pent_bb) false [] [("218_236",5);("218_236",3)];;
set_node_numerics t1;;
*)


(*
if a face is small the three edges lie in the range [2,2.25].
if an edge is in the range (2.25,2.52], then the face is big.
*)

let set_face_numerics bb = 
  let small = rotation bb.std3_small in
  let _ =  (intersect small bb.d_edge_225_252 = []) or failwith "set_face_numerics" in
  let adds = subtract small bb.d_edge_200_225 in
  let shortfields = (map (fun t-> ("e_200_225",t)) adds) in
  let r = map (C face_of_dart bb) (bb.d_edge_225_252) in
  let _ = (intersect (rotation bb.std3_small) r =[]) or failwith "set_face_numerics" in
  let bigfields = map (fun t -> ("bt",t)) (subtract r bb.std3_big) in
     modify_bb bb false (shortfields @ bigfields) [] ;;

(*
let t1 = modify_bb pent_bb false [("st",[9;6;10]);("e_225_252",[7;8;12])] [];;
set_face_numerics t1;;    
*)



(* ------------------------ *)
(* switch and selection functions *)

let switch3_of_dart d bb = 
  let c = face_of_dart d bb in 
  [modify_bb bb false ["bt",c] [];modify_bb bb false ["st",c] []];;

let switch_edge_of_dart d bb = 
      [modify_bb bb false ["e_225_252",d] [];modify_bb bb false ["e_200_225",d] []];; 



let dart_unsplit_of_std_tri bb =
  let xs = filter (fun t -> length t = 3) bb.std_faces_not_super in
  let split_nodes = bb.node_200_218 @ bb.node_218_252 in
  let split_edge = bb.d_edge_200_225 @ bb.d_edge_225_252 in
  let ys = rotation(filter (fun t -> subset t split_nodes) xs) in
     subtract ys split_edge;;

let switch_edge bb =   match dart_unsplit_of_std_tri bb  with
    | [] -> [bb]
    | d::_ -> switch_edge_of_dart d bb;;

let one_epass bbs = 
  let branches = flatten (map switch_edge bbs) in
  let _ =   echo bbs in
    filter_feas_f (fun s t -> t) branches;;

let switch3_edge bb =match bb.std_faces_not_super with
  |[] -> failwith ("switch3_edge empty: "^bb.hypermap_id)
  | fc::_ ->
  let fc' = rotateL 1 fc in 
  if not(mem fc (rotation (bb.std3_big @ bb.std3_small))) then
    [modify_bb bb true ["bt",fc] [];modify_bb bb true ["st",fc] []]
  else [modify_bb bb false ["e_225_252",fc';"bt",fc] [];modify_bb bb false ["e_200_225",fc'] []];;

let switch_node bb i = 
  if (i<0) then [bb] else
  [modify_bb bb false [] ["218_252",i];modify_bb bb false [] ["200_218",i]];;

let get_node bb = 
   let x = up (card_node bb) in
   let y = bb.node_218_252 @ bb.node_200_218 in
     try
       find (fun t -> not(mem t y)) x 
     with Not_found -> (-1);;

let get_high_node bb = 
   let x =bb.node_218_252 in
   let y = bb.node_236_252 @ bb.node_218_236 in
     try
       find (fun t -> not(mem t y)) x 
     with Not_found -> (-1);;

let switch_high_node bb i = 
  if (i<0) then [bb] else
  [modify_bb bb false [] ["236_252",i];modify_bb bb false [] ["218_236",i]];;

let one_highvpass bbs = 
  let switch_v bb = switch_high_node bb (get_high_node bb) in
  let branches = flatten (map switch_v bbs) in
  let _ = echo bbs in
    filter_feas branches;;

let onevpass bbs = 
  let switch_v bb = switch_node bb (get_node bb) in
  let branches = flatten (map switch_v bbs) in
  let _ =  echo bbs in
    filter_feas branches;;

let onevpassi bbs i =
 let branches = flatten (map (fun bb -> switch_node bb i) bbs) in
    filter_feas branches;;


let rec allpassdepth count bbs = 
   let bb = find_max bbs in
   let bbss = filter (fun t-> not(t = bb)) bbs in
      allpassdepth (count - 1) (onepass [bb]  @ bbss);;

let rec allvpass bbs = 
   if bbs = [] then [] 
   else
     let t = fold_right max (map get_node bbs) (-1) in
       if t < 0 then bbs else allvpass (onevpass bbs);;

let rec all_highvpass bbs = 
   if bbs = [] then [] 
   else
     let t = fold_right max (map get_high_node bbs) (-1) in
       if t < 0 then bbs else all_highvpass (one_highvpass bbs);;


