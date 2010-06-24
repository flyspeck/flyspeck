(* tests of the final cases... *)

Sys.command("pwd");;

(*
18839 cases in tame_bb
470 in feasible_bb
12 in hard_bb, so 99.936 % complete.

#directory "/Users/thomashales/Desktop/googlecode/flyspeck/glpk/";;
#use "glpk_link.ml";;
#use "tame_archive/lpproc.ml";;
let (tame_bb,feasible_bb,hard_bb,easy_bb,remaining_easy_bb) = Lpproc.execute();;
*)

(* build up hashtables of all the variables assignments from the dumpfile *)
let ynhash = Hashtbl.create 13;;
let yehash = Hashtbl.create 70;;
let azimhash = Hashtbl.create 70;;
let yn i = Hashtbl.find ynhash i;;
let ye (i,j) = Hashtbl.find yehash (i,j);;
let azim(i,j) = Hashtbl.find azimhash (i,j);;

let init_hash () = 
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

let get_dumpvar  s = (* read variables from dumpfile *)
  let com = sprintf "grep '%s' %s | sed 's/^.*= //'  " s dumpfile in
  let (ic,oc) = Unix.open_process(com) in
  let _ = close_out oc in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process(ic,oc) in
  inp;;
(* get_dumpvar "yn.0.*=";; *)


let float_of_dump s = float_of_string (hd s);;
let get_float s = float_of_dump(get_dumpvar s);;
let int_of_face xs bb = wheremod (faces bb) xs;;

let get_sol xs bb = get_float (sprintf "sol.%d.*=" (int_of_face xs bb));;
(* get_sol [12;7;8] bb;; *)

let get_tau xs bb = get_float (sprintf "tau.%d.*=" (int_of_face xs bb));;
(* get_tau [12;7;8] bb;; *)

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

(* experimental *)
let get_azim_diff f xs bb = 
   let [y1;y2;y3] = map yn xs in
   let [y6;y4;y5] = map (fun i -> ye (i,int_of_face xs bb)) xs in
   let a1 = azim (hd xs, int_of_face xs bb) in
   let b1 = f y1 y2 y3 y4 y5 y6 in
   abs_float (a1 -. b1);;
(* get_azim_diff dih_y [2;4;3] bb;;  *)

(* std triangles, heights set, and not already small/big edge split *)

let get_tri bb =
  let xs = filter (fun t -> length t = 3) bb.std_faces_not_super in
  let m i t = mem (nth t i) (bb.node_200_218 @ bb.node_218_252) in
  let ys = rotation(filter (fun t -> m 0 t && m 1 t && m 2 t) xs) in
  let zs = filter (fun t -> not(mem t (bb.d_edge_200_225 @ bb.d_edge_225_252))) ys in
   zs;;

(* experimental: first entry is the triangle with the biggest azim error. *)
let biggest_azim_diff f bb = 
  let _ = init_hash() in
  let ys = get_tri bb in 
  let u = map (fun t->  (get_azim_diff f t bb  ,t))  ys in
  let v = sort (fun a b -> - compare (fst a) (fst b)) u in
   v;;
(* biggest_azim_diff dih_y bb;;   *)


(*
let shuffle_face f bb = 
  let v = biggest_azim_diff f bb in
   if (v = []) then bb else
     let xs = snd(hd v) in
       modify_bb bb false ["sh",xs] [];;
*)
let shuffle_face f bb = bb;;  (* add details later *)

let shuffle t = shuffle_face dih_y t;;

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

let switch_edge bb = (* old *)
  match get_tri bb  with
    | [] -> [bb]
    | f::_ ->
      [modify_bb bb false ["e_225_252",f] [];modify_bb bb false ["e_200_225",f] []];; 

let one_epass bbs = 
  let branches = flatten (map switch_edge bbs) in
  let _ =   echo bbs in
    filter_feas_f shuffle branches;;

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

let hard_string = map(fun t -> t.string_rep) 
  (filter (fun t -> mem t.hypermap_id hardid) tame_bb);;

let findid s  = find (fun t -> s = t.hypermap_id);;
let findall s = filter (fun t -> s = t.hypermap_id);;
let tests = ref [];;


(* experimental section from here to the end of the file *)


(* std4_diag3 disappears: *)
length hard_bb;;  (* 12 *)


(*  doing case 86506100695 *)

length t8;; (* 1270 *)
find_max t8;;
let t865 = t8;;



let testsuper _ = 
  let allhardpassA_bb = allpass 3 hard_bb in 
  let allhardpassS_bb =  (filter (fun t -> length t.std4_diag3 >0) allhardpassA_bb) in
  let allhardpassF_bb =  filter (fun t -> ( length t.std4_diag3 = 0) && (length t.apex_sup_flat > 0))  allhardpassA_bb in 
    allhardpassS_bb = [] && allhardpassF_bb = [];; 

testsuper();;
tests := testsuper :: !tests;;


(* case 86506100695 *)
let h86 _ =
  let h86 = [findid "86506100695" hard_bb] in
  let h86a = allpass 10 h86 in
  let h86b = allpass 10  h86a in
    allvpass h86b = [];;
tests := h86 :: !tests;;


(* the 2 pressed icosahedra remain *)

let hard2_bb = filter (fun t -> mem t.hypermap_id ["161847242261";"223336279535"]) hard_bb;;


length hard2_bb;;
let h16 = allvpass (findall "161847242261" hard_bb);;
let h16max = find_max h16;;  (* 12.0627 *)
let b16 = h16;;
let b16a = all_highvpass b16;;
length b16a;;
let b16Amax = find_max b16a;; (* 12.0627 *)
let b16b =   (one_epass b16a);;
let b16c  = one_epass (one_epass b16b);;
let b16d = one_epass b16c;;
length b16d;;
let b16e = find_max b16d;;   (* 12.051 *)
0;; (* -- *)
let c16a= allpass 10 b16d;;
let c16Amax = find_max c16a;; (* 12.048 *)  (* was 12.059 *)
length c16a;;  (* 997 *)
let c16b = allpass 15 c16a;;
let c16Bmax = find_max c16b;;  (* 12.026 *) (* was 12.037 *)
length c16b;;  (* 657 *) (* was 636 *)



(*

(* this one is a dodecahedron modified with node 2 pressed
    into an edge *)
  let h  = findid (nth hardid 3);;  (* 12223336279535  *)
  let h1 = allpass [h];;
  length h1;;   (* length 1885 *)
  let k1 = find_max h1;;  (* 12.0416 *)
  let h2 = onevpassi h1 2;; (* length h2 : 2637 *)
(* unfinished... *)

(* this one is triangles only, types {6,0}, {4,0}, {6,0}. *)
  let r  = findid (nth hardid 5);;  (* 12161847242261  *)
  length r1;;   (* length  *)
  let r1 = allvpass [r];;
  let r2 = allpass r1;;
(* unfinished *)

*)




(*
let allhardpassB_bb = allpass 8 hard2_bb;;
*)

(*
let hard2_bb = [nth  hard_bb 0;nth hard_bb 1];;
(* to here *)

length (allhardpassB_bb);;  (* 288 *)
let h16 = find_max allhardpassB_bb;;
(* unfinished *)
*)

(*
let h0 = nth hard_bb 0;;
let h1 = 
  let s i l= flatten((map (fun t -> switch_node t i)) l) in
  let branches =   s 4(  s 3(  s 2(  s 1 (s 0 [h0])) ) )  in
   filter_feas branches;;
length h1;;
find_max h1;;
let all16_bb = allpass 6 h1;;
(* unfinished *)
*)

