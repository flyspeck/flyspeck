(*
Thomas C. Hales
June 25, 2009
Process linear programs for the proof of the Kepler conjecture.

needs new mktop on platforms that do not support dynamic loading of Str.

ocamlmktop unix.cma str.cma -o ocampl
./ocampl

glpk needs to be installed, and glpsol needs to be found in the path.
*)

(*
LoadAll to run all linear programs.
LoadFeasible skips tame_bb and loads feasible_bb.
NoLoad : load file without running linear programs.
*)


type mode = LoadFeasible | LoadAll | NoLoad;;  (* load mode *)
let mode = LoadAll;;

open Str;;
open List;;
let sprintf = Printf.sprintf;;

(* external files *)
let archiveraw = "/tmp/tame_graph.txt";; (*read only *)
let model = "/tmp/graph0.mod";; (* read only *)
let archive_feasible = "/tmp/feasible_graph.txt";; (* temporary out *)
let cpxfile = "/tmp/cplex.cpx";; (* temporary output *)
let tmpfile = "/tmp/graph.dat";;  (* temporary output *)

(* list operations *)
let maxlist0 xs = fold_right max xs 0;; (* NB: value is always at least 0 *)

let get_values key xs = 
  map snd (find_all (function k,_ -> (k=key)) xs);;

let upto = 
  let rec rangeA a i j  = if (i >= j) then a
   else rangeA ((j-1)::a) i (j-1)  in
  rangeA [] 0;;

let rec rotateL i xs = 
  if i=0 then xs 
  else match xs with
    | x::xss -> rotateL ((i-1) mod length xs) (xss @ [x])
    | [] -> [];;

let rotateR i = rotateL (-i);;

(* 
   zip from Harrison's lib.ml. 
   List.combine causes a stack overflow :
   let tt = upto 30000 in combine tt tt;;
   Stack overflow during evaluation (looping recursion?).
*)
let rec zip l1 l2 =
  match (l1,l2) with
        ([],[]) -> []
      | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
      | _ -> failwith "zip";;

let enumerate xs = zip (upto (length xs)) xs;;

let whereis i xs = 
  let (p,_) = find (function _,j -> j=i) (enumerate xs) in
    p;;

let rec nub = function
  | [] -> []
  | x::xs -> x::filter ((!=) x) (nub xs);;


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
  let (ic,oc) = Unix.open_process(sprintf "cat %s | grep -v '//' | grep -v '^$' | sed 's/\"[,]*//g' | sed 's/_//g' " filename) in
  let s = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
    s;;

(* read in the tame hypermap archive as java style strings *)

(* let tame = strip_archive archiveraw;;  *)
let tame = if (mode=NoLoad) then [] else 
                  if (mode = LoadAll) then (strip_archive archiveraw) 
		  else  strip_archive archive_feasible;;

length tame;;
(* example of java style string from hypermap generator. *)
let pentstring = "13_150834109178 18 3 0 1 2 3 3 2 7 3 3 0 2 4 5 4 0 3 4 6 1 0 4 3 7 2 8 3 8 2 1 4 8 1 6 9 3 9 6 10 3 10 6 4 3 10 4 5 4 5 3 7 11 3 10 5 11 3 11 7 12 3 12 7 8 3 12 8 9 3 9 10 11 3 11 12 9 ";;


(* conversion to list.  e.g. convert_to_list pentstring *)

(* 
   The order in which the faces occur is the order of branch n bound.
   The order affects the effectiveness of the branch and bound.
   My heuristic is to branch on hexagons, then quads, then pents, then tris.
   Within faces of a given size, look for vertices that appear frequently.
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
  let split_sp=  Str.split (regexp " ") in
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
    hypermapid : string;
    mutable lpvalue : float option;
    string_rep : string;
    std_faces_not_super: int list list;
    super8 : int list list;
    superduperq : int list list;
    bigtri : int list list;
    smalltri : int list list;
    (* special dart appears first in next ones *)
    superflat : int list list;
    flat_quarter : int list list;
    a_face : int list list;
    big5_face : int list list;
    big4_face : int list list;
    (* vertex lists *)
    highvertex : int list;
    lowvertex : int list;
  };;

(* conversion to branchnbound.  e.g. mk_bb pentstring  *)

let modify_bb bb drop1std fields vfields = 
  let add key xs = (@) (get_values key xs)  in
  let std = bb.std_faces_not_super in
{
hypermapid = bb.hypermapid;
lpvalue = None;
string_rep = bb.string_rep;
std_faces_not_super = if drop1std then tl std else std;
superflat = add "sf" fields bb.superflat;
super8 = add "s8" fields bb.super8;
superduperq = add "sd" fields bb.superduperq;
bigtri = add "bt" fields bb.bigtri;
smalltri = add "st" fields bb.smalltri;
flat_quarter = add "ff" fields bb.flat_quarter;
a_face = add "af" fields bb.a_face;
big5_face = add "b5" fields bb.big5_face;
big4_face = add "b4" fields bb.big4_face;
highvertex = add "hv" vfields bb.highvertex;
lowvertex = add "lv" vfields bb.lowvertex;
}
;;

(*
Example: move [8;1;6;9] from std to super8.
 let pbb = mk_bb pentstring;;
 modify_bb pbb true  ["s8",[8;1;6;9];"ff",[9;10;11]] ["lv",8;"hv",3;"lv",7];;
*)

let mk_bb s = 
  let (h,face1) = convert_to_list s in
 {hypermapid= h;
  lpvalue = None;
  string_rep=s;
  std_faces_not_super = face1;
  super8=[];
  superflat=[];
  superduperq=[];
  bigtri=[];
  smalltri=[];
  flat_quarter=[];
  a_face=[];
  big5_face=[];
  big4_face=[];
  highvertex=[];
  lowvertex=[];
 };;

let tame_bb = map mk_bb tame;; 


(* functions on branch n bound *)

let std_faces bb = bb.std_faces_not_super @ bb.super8 @ bb.superduperq @ bb.bigtri @ bb.smalltri;;

(* should sort faces, so that numbering doesn't change so much when branching *)

let faces bb = (std_faces bb) @ bb.superflat @ bb.flat_quarter @ 
  bb.a_face @ bb.big5_face @ bb.big4_face;;

let triples w = 
  let r j = nth w (j mod length w)  in
  let triple i = 
      [r i; r (i+1); r(i+2)] in
    map triple (upto (length w));;

let cvertex bb =
  1+ maxlist0 (flatten (faces bb));;

let cface bb = length(faces bb);;

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
  let number xs = map (fun i -> whereis i fs) xs in
  let list_of = unsplit " " string_of_int in
  let mk_faces xs = list_of (number xs) in
  let edart_raw  = 
    map triples fs in
  let edart =
    let edata_row (i,x) = (sprintf "(*,*,*,%d) " i)^(unsplit ", " list_of x) in
      unsplit "\n" edata_row (enumerate edart_raw) in 
  let mk_dart xs = sprintf "%d %d" (hd xs) (whereis xs fs) in
  let mk_darts xs = (unsplit ", " mk_dart xs) in
  let p = sprintf in
  let j = join_lines [
    p"param CVERTEX := %d;" (cvertex bb) ;
    p"param hypermapID := %s;" bb.hypermapid ; 
    p"param CFACE := %d;\n" (cface bb);
    p"set ITRIANGLE := %s;" (list_of (std_face_of_size bb 3)) ;
    p"set IQUAD := %s;" (list_of (std_face_of_size bb 4) );
    p"set IPENT := %s;" (list_of (std_face_of_size bb 5)) ;
    p"set IHEX := %s;\n" (list_of (std_face_of_size bb 6));
    p"set EDART := \n%s;\n"  (edart);
    p"set SUPER8 := %s;" (mk_faces bb.super8);
    p"set SUPERDUPERQ := %s;" (mk_faces bb.superduperq);
    p"set SUPERFLAT := %s;" (mk_darts bb.superflat);
    p"set FLAT := %s;" (mk_darts bb.flat_quarter);
    p"set APIECE := %s;" (mk_darts bb.a_face);
    p"set BIG5APEX := %s;" (mk_darts bb.big5_face);
    p"set BIG4APEX := %s;" (mk_darts bb.big4_face);
    p"set BIGTRI := %s;" (mk_faces bb.bigtri);
    p"set SMALLTRI := %s;"  (mk_faces bb.smalltri);
    p"set HIGHVERTEX := %s;" (list_of bb.highvertex);
    p"set LOWVERTEX := %s;" (list_of bb.lowvertex)] in
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

let solve_branch bb = (* side effects, lpvalue mutable *)
  let set_some bb r = (* side effects *)
    if (length r = 1) then bb.lpvalue <- Some (float_of_string(hd r)) else () in
  let com = sprintf "glpsol -m %s -d /dev/stdin | grep '^ln' | sed 's/lnsum = //' "  model in 
  let (ic,oc) = Unix.open_process(com) in 
  let _ = ampl_of_bb oc bb in
  let _ = close_out oc in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
  let _ = set_some bb inp in
  let r = match bb.lpvalue with
    | None -> -1.0
    | Some r -> r in
  let _ = Sys.command(sprintf "echo %s: %3.3f\n" bb.hypermapid r) in 
    bb;;

let solve bb = match bb.lpvalue with
  | None -> solve_branch bb
  | Some _ -> bb;;

(* display glpk messages *)

let display_lp bb = (* for debugging *)
  let oc = open_out tmpfile in
  let _ = ampl_of_bb oc bb in
  let _ = close_out oc in
  let com = sprintf "glpsol -m %s -d %s" model tmpfile in
  let _ = Sys.command(com) in 
    ();;

(* create cplex file without solving *)

let cpx_branch bb = (* debug *)
  let com = sprintf "glpsol -m %s --wcpxlp %s -d /dev/stdin | grep '^ln' | sed 's/lnsum = //' "  model cpxfile in 
  let (ic,oc) = Unix.open_process(com) in 
  let _ = ampl_of_bb oc bb in
  let _ = close_out oc in
  let _ = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
  sprintf "cplex file created of lp: %s" cpxfile;;


(* filtering output *)

let filterout_infeas f bbs = 
  let sol = map solve bbs in
    let fil ro = match ro.lpvalue with
	None -> true
      | Some r -> f r in 
      filter fil sol;;

let feasible r = (r > 11.999);; (* relax a bit from 12.0 *)


let feasible_bb = 
   if (mode = NoLoad) then [] 
     else if (mode = LoadAll) then (filterout_infeas feasible (map solve tame_bb))
       else tame_bb;;

length feasible_bb;; (* length 462 *)


let is_none bb = match bb.lpvalue with (* for debugging *)
    None -> true
  | Some _ -> false;;

let calc_max bbs = fold_right  (* for debugging *)
  (fun bb x -> match bb.lpvalue with
     |None -> x
     |Some y -> max x y) bbs 0.0;;

let find_max bbs = (* for debugging *)
  let r = Some (calc_max bbs) in
    find (fun bb -> r = bb.lpvalue) bbs;;

(* 
branching on face data:
switch_face does all the branching on the leading std face 
*)

let split_flatq xs i =  (* {y1,y3} is the new diagonal *)
  let y1::y2::y3::ys = rotateL i xs in
  ([y2;y3;y1],rotateR 1 (y1 :: y3 :: ys));;

let asplit_pent xs i = 
(* y2,y4 darts of flat; y3 is the point of the A, {y1,y3}, {y3,y5} diags *)
  let y1::y2::y3::y4::[y5] = rotateL i xs in
  ([y2;y3;y1],[y3;y5;y1],[y4;y5;y3]);;

let switch3 bb =
  let fc::_ = bb.std_faces_not_super in
  [modify_bb bb true ["bt",fc] [];modify_bb bb true ["st",fc] []];;


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
  let bbs = map f (upto 5) in
  let mo (a,b,c) = modify_bb bb true ["ff",a;"af",b;"ff",c] [] in
  let f i = mo (asplit_pent fc i) in
  let ccs = map f (upto 5) in
   (modify_bb bb true ["s8",fc] []) :: bbs @ ccs ;;

let switch6 bb = 
  let fc::_ = bb.std_faces_not_super in
  let mo (a,b) = modify_bb bb true ["ff",a;"b5",b] [] in
  let f i = mo (split_flatq fc i) in
   (modify_bb bb true ["s8",fc] []) :: (map f (upto 6));;

let switch_vertex bb i = 
  if (i<0) then [bb] else
  [modify_bb bb false [] ["hv",i];modify_bb bb false [] ["lv",i]];;

let get_vertex bb = 
   let x = upto (cvertex bb) in
   let y = bb.highvertex @ bb.lowvertex in
     try
       find (fun t -> not(mem t y)) x 
     with Not_found -> (-1);;

let switch_v bb = switch_vertex bb (get_vertex bb);;

let nextc = 
  let counter = ref 0 in
  fun () ->
    counter:= !counter + 1;
    !counter;;

let onevpass bbs = 
 let branches = flatten (map switch_v bbs) in
    Sys.command (sprintf "echo V STACK %d %d" (length bbs) (nextc()));
   filterout_infeas feasible branches;;

let onevpassi bbs i =
 let branches = flatten (map (fun bb -> switch_vertex bb i) bbs) in
    filterout_infeas feasible branches;;

let switch_face bb = match bb.std_faces_not_super with
  | [] -> [bb]
  | fc::_ ->
      let j = length fc in
      let fn = (nth [switch3;switch4;switch5;switch6] (j-3)) in
	fn bb;;

let onepass bbs = 
  let branches = flatten (map switch_face bbs) in
    Sys.command(sprintf "echo STACK %d %d" (length bbs) (nextc()));
    filterout_infeas feasible branches;;

let rec allpass count bbs = 
   let t = maxlist0 (map (fun b -> length b.std_faces_not_super) bbs) in
   if t = 0 or count <= 0 then bbs else allpass (count - 1) (onepass bbs);;

let rec allvpass bbs = 
   if bbs = [] then [] 
   else
     let t = fold_right max (map get_vertex bbs) (-1) in
       if t < 0 then bbs else allvpass (onevpass bbs);;

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


(* hard cases
"179189825656 21 4 0 1 2 3 3 0 3 4 3 4 3 2 3 4 2 5 3 5 2 6 3 6 2 1 3 6 1 7 3 7 1 8 3 8 1 0 3 8 0 9 3 9 0 4 3 9 4 10 3 10 4 5 3 10 5 11 3 11 5 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 ",
"154005963125 20 4 0 1 2 3 4 0 3 4 5 3 4 3 2 3 4 2 6 3 6 2 7 3 7 2 1 3 7 1 8 3 8 1 9 3 9 1 0 3 9 0 5 3 9 5 10 3 10 5 11 3 11 5 4 3 11 4 6 3 11 6 12 3 12 6 7 3 12 7 8 3 12 8 10 3 8 9 10 3 10 11 12 ",
"65974205892 19 4 0 1 2 3 4 0 3 4 5 3 4 3 6 3 6 3 2 3 6 2 7 3 7 2 8 3 8 2 1 3 8 1 9 4 9 1 0 5 3 9 5 10 3 10 5 4 3 10 4 11 3 11 4 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 ",
"223336279535 21 4 0 1 2 3 3 0 3 4 3 4 3 5 3 5 3 2 3 5 2 6 3 6 2 1 3 6 1 7 3 7 1 8 3 8 1 0 3 8 0 9 3 9 0 4 3 9 4 10 3 10 4 5 3 10 5 11 3 11 5 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 ",
"86506100695 20 4 0 1 2 3 4 0 3 4 5 3 4 3 6 3 6 3 2 3 6 2 7 3 7 2 1 3 7 1 8 3 8 1 9 3 9 1 0 3 9 0 5 3 9 5 10 3 10 5 11 3 11 5 4 3 11 4 6 3 11 6 12 3 12 6 7 3 12 7 8 3 12 8 10 3 8 9 10 3 10 11 12 ",
"161847242261 22 3 0 1 2 3 0 2 3 3 3 2 4 3 4 2 1 3 4 1 5 3 5 1 6 3 6 1 0 3 6 0 7 3 7 0 8 3 8 0 3 3 8 3 9 3 9 3 4 3 9 4 10 3 10 4 5 3 10 5 11 3 11 5 6 3 11 6 7 3 11 7 12 3 12 7 8 3 12 8 9 3 12 9 10 3 10 11 12 ",
*)

let findid s  = find (fun t -> s = t.hypermapid);;
let findall s = filter (fun t -> s = t.hypermapid);;
let tests = ref [];;

let (hard_bb,easy_bb) = partition (fun t -> (mem t.hypermapid hardid)) feasible_bb;;

let alleasypass_bb _ = allvpass (allpass 20 easy_bb);;
tests :=  (fun t -> alleasypass_bb t = [])::!tests;;

(* experimental section from here to the end of the file *)


(* superduperq disappears: *)
length hard_bb;;  (* 3 *)
let testsuper _ = 
  let allhardpassA_bb = allpass 3 hard_bb in 
  let allhardpassS_bb =  (filter (fun t -> length t.superduperq >0) allhardpassA_bb) in
  let allhardpassF_bb =  filter (fun t -> ( length t.superduperq = 0) && (length t.superflat > 0))  allhardpassA_bb in 
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

let hard2_bb = filter (fun t -> mem t.hypermapid ["161847242261";"223336279535"]) hard_bb;;

length hard2_bb;;
let h16 = allvpass (findall "161847242261" hard_bb);;
let h16max = find_max h16;;  (* 12.062 *)
let h16a= allpass 10 h16;;
let h16Amax = find_max h16a;;  (* 12.059 *)
let h16b = allpass 15 h16a;;
let h16Bmax = find_max h16b;;  (* 12.037 *)

length h16a;; (* 466 *)
length h16b;;  (* 636 *)



1;;
(*

(* this one is a dodecahedron modified with vertex 2 pressed
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
  let s i l= flatten((map (fun t -> switch_vertex t i)) l) in
  let branches =   s 4(  s 3(  s 2(  s 1 (s 0 [h0])) ) )  in
   filterout_infeas feasible branches;;
length h1;;
find_max h1;;
let all16_bb = allpass 6 h1;;
(* unfinished *)
*)

