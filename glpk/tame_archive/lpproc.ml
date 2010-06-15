(*
Thomas C. Hales
June 25, 2009
Process linear programs for the proof of the Kepler conjecture.

needs new mktop on platforms that do not support dynamic loading of Str.

ocamlmktop unix.cma nums.cma str.cma -o ocampl
./ocampl

glpk needs to be installed, and glpsol needs to be found in the path.
*)


open Str;;
open List;;
let sprintf = Printf.sprintf;;

type mode =  LoadAll | NoLoad;;  (* load mode *)
let mode = LoadAll;;

let nextc = 
  let counter = ref 0 in
  fun () ->
    counter:= !counter + 1;
    !counter;;

(* external files *)
let archiveraw = "/tmp/tame_graph.txt";; (*read only *)
let model = "/tmp/graph0.mod";; (* read only *)
let archive_feasible = "/tmp/feasible_graph.txt";; (* temporary out *)
let cpxfile = "/tmp/cplex.cpx";; (* temporary output *)
let tmpfile = "/tmp/graph.dat";;  (* temporary output *)
let dumpfile = "/tmp/graph.out";; (* temp output *)

(* list operations *)
let maxlist0 xs = fold_right max xs 0;; (* NB: value is always at least 0 *)

let get_values key xs = 
  map snd (find_all (function k,_ -> (k=key)) xs);;

let up = 
  let rec rangeA a i j  = if (i >= j) then a
   else rangeA ((j-1)::a) i (j-1)  in
  rangeA [] 0;;

let rec rotateL i xs = 
  if i=0 then xs 
  else match xs with
    | x::xss -> rotateL ((i-1) mod length xs) (xss @ [x])
    | [] -> [];;

let rotateR i = rotateL (-i);;

let rotation xs = 
  let maxsz = maxlist0 (map length xs) in
  flatten (map (fun i -> map (rotateL i) xs) (up maxsz));;


(* 
   zip from Harrison's lib.ml. 
   List.combine causes a stack overflow :
   let tt = up 30000 in combine tt tt;;
   Stack overflow during evaluation (looping recursion?).
*)
let rec zip l1 l2 =
  match (l1,l2) with
        ([],[]) -> []
      | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
      | _ -> failwith "zip";;

let enumerate xs = zip (up (length xs)) xs;;

let whereis i xs = 
  let (p,_) = find (function _,j -> j=i) (enumerate xs) in
    p;;

let wheremod xs x = 
  let ys = rotation xs in 
   (whereis x ys) mod (length xs);;

(* example *)
wheremod [[0;1;2];[3;4;5];[7;8;9]] [8;9;7];;  (* 2 *)

let rec nub = function
  | [] -> []
  | x::xs -> x::filter ((<>) x) (nub xs);;  (* was physical != *)


(* read and write *)

let load_and_close_channel do_close ic = 
  let rec lf ichan a = 
    try
      lf ic (input_line ic::a)
    with End_of_file -> a in
    let rs = lf ic [] in
      if do_close then close_in ic else ();
      rev rs;;

let load_file filename = 
  let ic = open_in filename in load_and_close_channel true ic;;

let save_stringarray filename xs = 
  let oc = open_out filename in
    for i=0 to length xs -1
    do
      output_string oc (nth xs i ^ "\n");
      done;
    close_out oc;;

let strip_archive filename =  (* strip // comments, blank lines, quotes etc. *)
  let (ic,oc) = Unix.open_process(sprintf "cat %s | grep -v '//' | grep -v '^$' | sed 's/\"[,;]*//g' | sed 's/_//g' " filename) in
  let s = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
    s;;

(* read in the tame hypermap archive as java style strings *)

(* let tame = strip_archive archiveraw;;  *)
let tame = if (mode=NoLoad) then [] else strip_archive archiveraw;;

length tame;;
(* example of java style string from hypermap generator. *)
let pentstring = "13_150834109178 18 3 0 1 2 3 3 2 7 3 3 0 2 4 5 4 0 3 4 6 1 0 4 3 7 2 8 3 8 2 1 4 8 1 6 9 3 9 6 10 3 10 6 4 3 10 4 5 4 5 3 7 11 3 10 5 11 3 11 7 12 3 12 7 8 3 12 8 9 3 9 10 11 3 11 12 9 ";;


(* conversion to list.  e.g. convert_to_list pentstring *)

(* 
   The order in which the faces occur is the order of branch n bound.
   The order affects the effectiveness of the branch and bound.
   My heuristic is to branch on hexagons, then quads, then pents, then tris.
   Within faces of a given size, look for nodes that appear frequently.
*)
let order_list (h,xs) = 
  let fl = flatten xs in
  let count k = length (filter ((=) k) fl) in
  let mc rs = maxlist0 (map count rs) in
  let sortfn a b = compare (mc b) (mc a) in
  let r k = filter (fun x -> length x = k) xs in
  let f k = sort sortfn (r k) in
   (h,f 6 @ f 4 @ f 5 @ f 3);;

(*
let test = [[1;99;77];[2;3;7];[9;10;11;12];[1;2;3;7];[1;2;3;4];[11;3;13;14;15];[16;17;18;19;20;21];[1;2;3;4;5]];;
*)

let convert_to_list = 
  let split_sp=  Str.split (regexp " +") in
  let strip_ = global_replace (regexp "_") "" in
  let rec movelist n (x,a) = 
    if n=0 then (x,a) else match x with y::ys -> movelist (n-1) (ys, y::a) in
  let getone (x,a) = match x with
    | [] -> ([],a)
    | y::ys -> let (u,v) = movelist y (ys,[]) in (u,v::a) in 
  let rec getall (x,a) =
    if (x=[]) then (x,a) else getall (getone (x,a)) in
  fun s ->
    let h::ss = (split_sp (strip_ s)) in
    let _::ns = map int_of_string ss in
    let (_,a) = getall (ns,[]) in
    order_list (h,rev (map rev a));;



(* type for holding the parameters for a linear program *)

type branchnbound = 
  { 
    hypermap_id : string;
    mutable lpvalue : float option;
    mutable hints : int list list;  (* hints about branching *) 
    string_rep : string;
    std_faces_not_super: int list list;
    std56_flat_free : int list list;
    std4_diag3 : int list list;
    std3_big : int list list;
    std3_small : int list list;
    (* special dart appears first in next ones *)
    apex_sup_flat : int list list;
    apex_flat : int list list;
    apex_A : int list list;
    apex5 : int list list;
    apex4 : int list list;
    (* edge lists *)
    d_edge_225_252 :  int list list;
    d_edge_200_225 :  int list list;
    (* node lists *)
    node_218_252 : int list;
    node_236_252 : int list;
    node_218_236 : int list;
    node_200_218 : int list;
  };;

let mk_bb s = 
  let (h,face1) = convert_to_list s in
 {hypermap_id= h;
  lpvalue = None;
  hints = [];;
  string_rep=s;
  std_faces_not_super = face1;
  std56_flat_free=[];
  apex_sup_flat=[];
  std4_diag3=[];
  std3_big=[];
  std3_small=[];
  apex_flat=[];
  apex_A=[];
  apex5=[];
  apex4=[];
  d_edge_225_252=[];
  d_edge_200_225=[];
  node_218_252=[];
  node_236_252=[];
  node_218_236=[];
  node_200_218=[];
 };;

let pent_bb = mk_bb pentstring;;
let tame_bb = map mk_bb tame;; 


(* conversion to branchnbound.  e.g. mk_bb pentstring  *)




let modify_bb bb drop1std fields vfields = 
  let add key xs t = nub ((get_values key xs) @ t)  in
  let shuffle key xs vs = 
    let ys = get_values key xs in 
    let e = rotation ys in
      nub(ys @ (filter (fun t -> not(mem t e)) vs)) in 
  let std = bb.std_faces_not_super in
  let shuffle_std = shuffle "sh" fields std in 
{
hypermap_id = bb.hypermap_id;
lpvalue = None;
hints = bb.hints;
string_rep = bb.string_rep;
std_faces_not_super = if drop1std then tl std else shuffle_std;
apex_sup_flat = add "sf" fields bb.apex_sup_flat;
std56_flat_free = add "s8" fields bb.std56_flat_free;
std4_diag3 = add "sd" fields bb.std4_diag3;
std3_big = add "bt" fields bb.std3_big;
std3_small = add "st" fields bb.std3_small;
apex_flat = add "ff" fields bb.apex_flat;
apex_A = add "af" fields bb.apex_A;
apex5 = add "b5" fields bb.apex5;
apex4 = add "b4" fields bb.apex4;
d_edge_225_252 = add "be" fields bb.d_edge_225_252;
d_edge_200_225 = add "se" fields bb.d_edge_200_225;
node_218_252 = add "hv" vfields bb.node_218_252;
node_236_252 = add "ehv" vfields bb.node_236_252;
node_218_236 = add "mhv" vfields bb.node_218_236;
node_200_218 = add "lv" vfields bb.node_200_218;
}
;;



(*
Example: move [8;1;6;9] from std to std56_flat_free.

modify_bb pent_bb true  ["s8",[8;1;6;9];"ff",[9;10;11]] ["lv",8;"hv",3;"lv",7];;
pent_bb;;
modify_bb pent_bb false ["sh",[0;3;5;4];"sh",[10;6;4]] [];;
*)

(* functions on branch n bound *)

let std_faces bb = bb.std_faces_not_super @ bb.std56_flat_free @ bb.std4_diag3;;
(*  @ bb.std3_big @ bb.std3_small;; *)

let std_tri_prebranch bb = filter 
   (let r = rotation (bb.std3_big @ bb.std3_small) in
       fun t -> not(mem t r)  && (length t = 3)) bb.std_faces_not_super;;

(* should sort faces, so that numbering doesn't change so much when branching *)

let faces bb = (std_faces bb) @ bb.apex_sup_flat @ bb.apex_flat @ 
  bb.apex_A @ bb.apex5 @ bb.apex4;;

let triples w = 
  let r j = nth w (j mod length w)  in
  let triple i = 
      [r i; r (i+1); r(i+2)] in
    map triple (up (length w));;

let card_node bb =
  1+ maxlist0 (flatten (faces bb));;

let card_face bb = length(faces bb);;

let std_face_of_size bb r= 
  let f = std_faces bb in
  let z = enumerate f in 
    fst(split (filter (function _,y -> length y=r) z));;


(* generate ampl data string of branch n bound *)

let unsplit d f = function
  | (x::xs) ->  fold_left (fun s t -> s^d^(f t)) (f x) xs
  | [] -> "";;

let join_lines  = unsplit "\n" (fun x-> x);;



let ampl_of_bb outs bb = 
  let fs = faces bb in
  let where3 = wheremod fs in
(*
  let maxsz = maxlist0 (map length fs) in
  let fs3 = flatten (map (fun i -> map (rotateL i) fs) (up maxsz)) in
  let fs3 = fs @ map (rotateL 1) fs @ map (rotateL 2) fs @ map (rotateL 3) fs @ map (rotateL 4) fs in 
  let where3 i = (whereis i fs3) mod (length fs) in 
*)
  let number = map where3 in
  let list_of = unsplit " " string_of_int in
  let mk_faces xs = list_of (number xs) in
  let e_dart_raw  = 
    map triples fs in
  let e_dart =
    let edata_row (i,x) = (sprintf "(*,*,*,%d) " i)^(unsplit ", " list_of x) in
      unsplit "\n" edata_row (enumerate e_dart_raw) in 
  let mk_dart xs = sprintf "%d %d" (hd xs) (where3 xs) in
  let mk_darts xs = (unsplit ", " mk_dart xs) in
  let p = sprintf in
  let j = join_lines [
    p"param card_node := %d;" (card_node bb) ;
    p"param hypermap_id := %s;" bb.hypermap_id ; 
    p"param card_face := %d;\n" (card_face bb);
    p"set std3 := %s;" (list_of (std_face_of_size bb 3)) ;
    p"set std4 := %s;" (list_of (std_face_of_size bb 4) );
    p"set std5 := %s;" (list_of (std_face_of_size bb 5)) ;
    p"set std6 := %s;\n" (list_of (std_face_of_size bb 6));
    p"set e_dart := \n%s;\n"  (e_dart);
    p"set std56_flat_free := %s;" (mk_faces bb.std56_flat_free);
    p"set std4_diag3 := %s;" (mk_faces bb.std4_diag3);
    p"set apex_sup_flat := %s;" (mk_darts bb.apex_sup_flat);
    p"set apex_flat := %s;" (mk_darts bb.apex_flat);
    p"set apex_A := %s;" (mk_darts bb.apex_A);
    p"set apex5 := %s;" (mk_darts bb.apex5);
    p"set apex4 := %s;" (mk_darts bb.apex4);
    p"set d_edge_225_252 := %s;" (mk_darts bb.d_edge_225_252);
    p"set d_edge_200_225 := %s;" (mk_darts bb.d_edge_200_225);
    p"set std3_big := %s;" (mk_faces bb.std3_big);
    p"set std3_small := %s;"  (mk_faces bb.std3_small);
    p"set node_218_252 := %s;" (list_of bb.node_218_252);
    p"set node_236_252 := %s;" (list_of bb.node_236_252);
    p"set node_218_236 := %s;" (list_of bb.node_218_236);
    p"set node_200_218 := %s;" (list_of bb.node_200_218)] in
    Printf.fprintf outs "%s" j;;  

(* display ampl file without solving *)

let display_ampl bb = (* for debugging *)
  let file = tmpfile in 
  let outs = open_out file in
  let _ = ampl_of_bb outs bb in
  let _ = close_out outs in
    Sys.command(sprintf "cat %s" file);;

let testps() =  (* for debugging *)
  let bb = mk_bb pentstring in
  let bb =  modify_bb bb false ["ff",[0;1;2];"sd",[5;3;7;11];"ff",[12;7;8]] ["hv",8] in
    display_ampl bb;;




(* running of branch in glpsol *)

let solve_branch_f addhints bb = (* side effects, lpvalue & hints mutable *)
  let set_some bb r = (* side effects *)
    if (length r = 1) then bb.lpvalue <- Some (float_of_string(hd r)) else () in
  let com = sprintf "glpsol -m %s -d /dev/stdin | tee %s | grep '^ln' | sed 's/lnsum = //' "  model dumpfile in 
  let (ic,oc) = Unix.open_process(com) in 
  let _ = ampl_of_bb oc bb in
  let _ = close_out oc in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
  let _ = addhints bb in (* hints for control flow *)
  let _ = set_some bb inp in
  let r = match bb.lpvalue with
    | None -> -1.0
    | Some r -> r in
  let _ = Sys.command(sprintf "echo %s: %3.3f\n" bb.hypermap_id r) in 
    bb;;

let solve_f f bb = match bb.lpvalue with
  | None -> solve_branch_f f bb
  | Some _ -> bb;;

let solve bb = solve_f (fun t -> t) bb;;

(* filtering output *)

let filter_feas_f f bbs = 
  let feasible r = (r > 11.999) in (* relax a bit from 12.0 *)
  let sol = map (fun t -> solve_f f t) bbs in
    let fil ro = match ro.lpvalue with
	None -> true
      | Some r -> feasible r in 
      filter fil sol;;

let filter_feas bbs = filter_feas_f (fun t->t) bbs;;




(* for debugging : display glpk output *)

let display_lp bb = 
  let oc = open_out tmpfile in
  let _ = ampl_of_bb oc bb in
  let _ = close_out oc in
  let com = sprintf "glpsol -m %s -d %s | tee %s" model tmpfile dumpfile in
  let _ = Sys.command(com) in 
    ();;

(* for debugging: create cplex file without solving *)

let cpx_branch bb = (* debug *)
  let com = sprintf "glpsol -m %s --wcpxlp %s -d /dev/stdin | grep '^ln' | sed 's/lnsum = //' "  model cpxfile in 
  let (ic,oc) = Unix.open_process(com) in 
  let _ = ampl_of_bb oc bb in
  let _ = close_out oc in
  let _ = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
  sprintf "cplex file created of lp: %s" cpxfile;;

(* for debugging: reading optimal variables values from the dumpfile *)

let get_dumpvar  s = (* read variables from dumpfile *)
  let com = sprintf "grep '%s' %s | sed 's/^.*= //'  " s dumpfile in
  let (ic,oc) = Unix.open_process(com) in
  let _ = close_out oc in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process(ic,oc) in
  inp;;
(* get_dumpvar "yn.0.*=";; *)

(* build up hashtables of all the variables assignments from the dumpfile *)

let ynhash = Hashtbl.create 13;;
let yehash = Hashtbl.create 70;;
let azimhash = Hashtbl.create 70;;
let yn i = Hashtbl.find ynhash i;;
let ye (i,j) = Hashtbl.find yehash (i,j);;
let azim(i,j) = Hashtbl.find azimhash (i,j);;

let init_hash () = 
  let com = sprintf "cat %s | grep -v ':'  | grep '=' | tr '[\[\]=,]' ' ' | sed 's/\( [0-9]*\)$/\1.0/g'" dumpfile in
  let (ic,oc) = Unix.open_process(com) in
  let _  = close_out oc in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process(ic,oc) in
  let split_sp=  Str.split (regexp " +") in
  let inpa = map split_sp inp in
  let _ = Hashtbl.clear ynhash in
  let _ = Hashtbl.clear yehash in
  let _ = Hashtbl.clear azimhash in
  let ynproc [a;b;c] = Hashtbl.add ynhash (int_of_string b) (float_of_string c) in
  let yeproc [a;b;c;d] = Hashtbl.add yehash ( (int_of_string b), (int_of_string c)) (float_of_string d) in
  let azimproc [a;b;c;d] = Hashtbl.add azimhash ( (int_of_string b), (int_of_string c)) (float_of_string d) in
  let proc1 xs = 
    let a = hd xs in
      if (a = "yn") then ynproc xs
      else if (a = "ye") then yeproc xs
      else if (a = "azim") then azimproc xs in
  let _ = map proc1 inpa in ();;
(* init_hash ();; *)

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

(* 
branching on face data:
switch_face does all the branching on the leading std face 
*)


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


let split_flatq xs i =  (* {y1,y3} is the new diagonal *)
  let y1::y2::y3::ys = rotateL i xs in
  ([y2;y3;y1],rotateR 1 (y1 :: y3 :: ys));;

let asplit_pent xs i = 
(* y2,y4 darts of flat; y3 is the point of the A, {y1,y3}, {y3,y5} diags *)
  let y1::y2::y3::y4::[y5] = rotateL i xs in
  ([y2;y3;y1],[y3;y5;y1],[y4;y5;y3]);;

(*
let switch_edge bb =
  let l = bb.node_200_218 in
  let h = bb.node_218_252 in
  let m t i r = mem (nth (fst t) i) r in
  let faces = filter (fun t ->  length t = 3) (std_faces bb) in
  let face2 = flatten (map (fun t -> [(t,t); (rotateL 1 t,t); (rotateL 2 t,t)]) faces) in
  let face3 = filter (fun t -> m t 0 l && m t 1 l && m t 2 h) face2 in 
  let face4 = filter (fun t -> not (mem (fst t) (bb.d_edge_225_252 @ bb.d_edge_200_225))) face3 in
  if (face4=[]) then [bb] else 
    let (f,_)::_ = face4 in
      [modify_bb bb false ["be",f] [];modify_bb bb false ["se",f] []];; 
*)

let switch_edge bb = (* old *)
  let face  = get_tri bb in
    if (face = []) then [bb] 
    else  let f::_ = face in
      [modify_bb bb false ["be",f] [];modify_bb bb false ["se",f] []];; 

let switch3 bb = 
  let fc::_ = std_tri_prebranch bb  in
  [modify_bb bb false ["bt",fc] [];modify_bb bb false ["st",fc] []];;

let switch3_edge bb =
  let fc::_ =  bb.std_faces_not_super  in
  let fc' = rotateL 1 fc in 
  if not(mem fc (rotation (bb.std3_big @ bb.std3_small))) then
    [modify_bb bb true ["bt",fc] [];modify_bb bb true ["st",fc] []]
  else [modify_bb bb false ["be",fc';"bt",fc] [];modify_bb bb false ["se",fc'] []];;

let switch4 bb = 
  let fc::_ = bb.std_faces_not_super in
  let mo s (a,b) = modify_bb bb true [s,a;s,b] [] in
  let f s i = mo s (split_flatq fc i) in
  let g s = modify_bb bb true [s,fc] [] in
  [f "ff" 0;f "ff" 1; f "sf" 0; f "sf" 1;g "sd"];;


let switch5 bb = 
  let fc::_ = bb.std_faces_not_super in
  let mo (a,b) = modify_bb bb true ["ff",a;"b4",b] [] in    
  let f i = mo (split_flatq fc i) in
  let bbs = map f (up 5) in
  let mo (a,b,c) = modify_bb bb true ["ff",a;"af",b;"ff",c] [] in
  let f i = mo (asplit_pent fc i) in
  let ccs = map f (up 5) in
   (modify_bb bb true ["s8",fc] []) :: bbs @ ccs ;;

let switch6 bb = 
  let fc::_ = bb.std_faces_not_super in
  let mo (a,b) = modify_bb bb true ["ff",a;"b5",b] [] in
  let f i = mo (split_flatq fc i) in
   (modify_bb bb true ["s8",fc] []) :: (map f (up 6));;

let switch_node bb i = 
  if (i<0) then [bb] else
  [modify_bb bb false [] ["hv",i];modify_bb bb false [] ["lv",i]];;

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
  [modify_bb bb false [] ["ehv",i];modify_bb bb false [] ["mhv",i]];;

let one_highvpass bbs = 
  let switch_v bb = switch_high_node bb (get_high_node bb) in
  let branches = flatten (map switch_v bbs) in
    Sys.command (sprintf "echo V STACK %d %d" (length bbs) (nextc()));
    filter_feas branches;;

let one_epass bbs = 
  let branches = flatten (map switch_edge bbs) in
    Sys.command (sprintf "echo V STACK %d %d" (length bbs) (nextc()));
    filter_feas_f shuffle branches;;

let onevpass bbs = 
  let switch_v bb = switch_node bb (get_node bb) in
  let branches = flatten (map switch_v bbs) in
    Sys.command (sprintf "echo V STACK %d %d" (length bbs) (nextc()));
    filter_feas branches;;

let onevpassi bbs i =
 let branches = flatten (map (fun bb -> switch_node bb i) bbs) in
    filter_feas branches;;

let switch_face bb = match bb.std_faces_not_super with
  | [] -> [bb]
  | fc::_ ->
      let j = length fc in
      let fn = (nth [switch3;switch4;switch5;switch6] (j-3)) in
	fn bb;;

let onepass bbs = 
  let branches = flatten (map switch_face bbs) in
    Sys.command(sprintf "echo STACKSIZE=%d COUNT=%d" (length bbs) (nextc()));
    filter_feas branches;;

let rec allpass count bbs = 
   let t = maxlist0 (map (fun b -> length (std_tri_prebranch b)) bbs) in
   if t = 0 or count <= 0 then bbs else allpass (count - 1) (onepass bbs);;

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

(* running the branching code on the feasible cases *)

let hardid = 
[
(* {3,3,3,3,3,3} *) "161847242261";
(* {3,3,3,3,3,3} *) "223336279535";
(* {3,3,3,3,3,3} *) "86506100695";
(* (* one quad {3,3,4} *) "179189825656"; 
(* two quad {3,4,4} *) "154005963125";
(* {4,4,4} *) "65974205892"; *)
];;

let hard_string = [
"179189825656 21 4 0 1 2 3 3 0 3 4 3 4 3 2 3 4 2 5 3 5 2 6 3 6 2 1 3 6 1 7 3 7 1 8 3 8 1 0 3 8 0 9 3 9 0 4 3 9 4 10 3 10 4 5 3 10 5 11 3 11 5 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 ";
"154005963125 20 4 0 1 2 3 4 0 3 4 5 3 4 3 2 3 4 2 6 3 6 2 7 3 7 2 1 3 7 1 8 3 8 1 9 3 9 1 0 3 9 0 5 3 9 5 10 3 10 5 11 3 11 5 4 3 11 4 6 3 11 6 12 3 12 6 7 3 12 7 8 3 12 8 10 3 8 9 10 3 10 11 12 ";
"65974205892 19 4 0 1 2 3 4 0 3 4 5 3 4 3 6 3 6 3 2 3 6 2 7 3 7 2 8 3 8 2 1 3 8 1 9 4 9 1 0 5 3 9 5 10 3 10 5 4 3 10 4 11 3 11 4 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 ";
"223336279535 21 4 0 1 2 3 3 0 3 4 3 4 3 5 3 5 3 2 3 5 2 6 3 6 2 1 3 6 1 7 3 7 1 8 3 8 1 0 3 8 0 9 3 9 0 4 3 9 4 10 3 10 4 5 3 10 5 11 3 11 5 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 ";
"86506100695 20 4 0 1 2 3 4 0 3 4 5 3 4 3 6 3 6 3 2 3 6 2 7 3 7 2 1 3 7 1 8 3 8 1 9 3 9 1 0 3 9 0 5 3 9 5 10 3 10 5 11 3 11 5 4 3 11 4 6 3 11 6 12 3 12 6 7 3 12 7 8 3 12 8 10 3 8 9 10 3 10 11 12 ";
"161847242261 22 3 0 1 2 3 0 2 3 3 3 2 4 3 4 2 1 3 4 1 5 3 5 1 6 3 6 1 0 3 6 0 7 3 7 0 8 3 8 0 3 3 8 3 9 3 9 3 4 3 9 4 10 3 10 4 5 3 10 5 11 3 11 5 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 "
];;

let findid s  = find (fun t -> s = t.hypermap_id);;
let findall s = filter (fun t -> s = t.hypermap_id);;
let tests = ref [];;

let feasible_bb =  filter_feas (map solve tame_bb);;


length feasible_bb;; (* length 462 *)

let (hard_bb,easy_bb) = partition (fun t -> (mem t.hypermap_id hardid)) feasible_bb;;

let alleasypass_bb _ = allvpass (allpass 20 easy_bb);;
tests :=  (fun t -> alleasypass_bb t = [])::!tests;;


(* experimental section from here to the end of the file *)


(* std4_diag3 disappears: *)
length hard_bb;;  (* 3 *)
let testsuper _ = 
  let allhardpassA_bb = allpass 3 hard_bb in 
  let allhardpassS_bb =  (filter (fun t -> length t.std4_diag3 >0) allhardpassA_bb) in
  let allhardpassF_bb =  filter (fun t -> ( length t.std4_diag3 = 0) && (length t.apex_sup_flat > 0))  allhardpassA_bb in 
    allhardpassS_bb = [] && allhardpassF_bb = [];; 
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

