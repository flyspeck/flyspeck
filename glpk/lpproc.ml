(*
Thomas C. Hales
June 25, 2009
Process linear programs for the proof of the Kepler conjecture.

needs to use ocamlstr (new top level with Str preloaded) on platforms that do not support dynamic loading of Str.

ocamlmktop unix.cma str.cma -o ocampl
./ocampl

*)
open Str;;
open List;;
let sprintf = Printf.sprintf;;

(* external files *)
let archiveraw = "/tmp/tame_graph.txt";;
let model = "/tmp/graph0.mod";;
let archive_tame_hi = "/tmp/tamehi.txt";; (* output *)

(* list operations *)
let maxlist0 xs = fold_right max xs 0;; (* NB: always at least 0 *)

let range = 
  let rec rangeA a i j  = if (i >= j) then a
   else rangeA ((j-1)::a) i (j-1)  in
  rangeA [];;

let rec rotateL i xs = 
  if (i<=0) then xs 
  else match xs with
    | x::xss -> rotateL (i-1) (xss @ [x])
    | [] -> [];;

let rec rotateTo xs i repmax = 
  match xs with
    | [] -> []
    | x::xss -> if (x=i) then xs else
	if(repmax<0) then raise (Failure "element not found") 
	else rotateTo (rotateL 1 xs) i (repmax-1);;


(* canonical order of cyclic list with distinct entries *)
let canon xs =
  let m = fold_right min xs (hd xs) in (rotateTo xs m (length xs));;

(* 
   zip from Harrison's lib.ml. 
   List.combine causes a stack overflow :
   let tt = range 0 30000 in combine tt tt;;
   Stack overflow during evaluation (looping recursion?).
*)
let rec zip l1 l2 =
  match (l1,l2) with
        ([],[]) -> []
      | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
      | _ -> failwith "zip";;

let enumerate xs = zip (range 0 (length xs)) xs;;

let whereis i xs = 
  let (p,_) = find (fun (_,j) -> (j=i)) (enumerate xs) in
    p;;



(* read and write *)

let load_and_close_channel do_close ic = 
  let rec lf ichan a = 
    try
      lf ic ((input_line ic)::a)
    with End_of_file -> a in
    let rs = lf ic [] in
      if (do_close) then close_in ic else ();
      rev rs;;

let load_file filename = 
  let ic = open_in filename in load_and_close_channel true ic;;

let save_stringarray filename xs = 
  let oc = open_out filename in
    for i=0 to length(xs) -1
    do
      output_string oc ((nth xs i)^"\n");
      done;
    close_out oc;;

let strip_archive filename =  (* strip // comments, blank lines, quotes etc. *)
  let (ic,oc) = Unix.open_process(sprintf "cat %s | grep -v '//' | grep -v '^$' | sed 's/\"[,]*//g' | sed 's/_//g' " filename) in
  let s = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
    s;;

(* read in the tame hypermap archive as java style strings *)

let tame = strip_archive archiveraw;;

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


(* conversion to branchnbound.  e.g. mk_bb pentstring  *)

type branchnbound = 
  { 
    hypermapid : string;
    string_rep : string;
    (* should be in canonical order: *)
    std_faces_not_super: int list list;
    super8 : int list list;
    bigtri : int list list;
    smalltri : int list list;
    (* special dart appears first *)
    flat_face : int list list;
    a_face : int list list;
    big5_face : int list list;
    big4_face : int list list;
    (* vertex lists *)
    highvertex : int list;
    lowvertex : int list;
  };;

let mk_bb s = 
  let (h,face1) = convert_to_list s in
 {hypermapid= h;
  string_rep=s;
  std_faces_not_super = face1;
  super8=[];
  bigtri=[];
  smalltri=[];
  flat_face=[];
  a_face=[];
  big5_face=[];
  big4_face=[];
  highvertex=[];
  lowvertex=[];
 };;
let tame_bb = map mk_bb tame;; 


(* functions on branch n bound *)

let faces bd = bd.std_faces_not_super @ bd.super8 @ 
  bd.smalltri @ bd.a_face @ bd.big5_face @ bd.big4_face;;

let std_faces bd = bd.std_faces_not_super @ bd.super8;;

let triples w = 
  let r j = nth w (j mod length w)  in
  let triple i = 
      [r i; r (i+1); r(i+2)] in
    map triple (range 0 (length w));;

let cvertex bb =
  1+ maxlist0 (flatten (faces bb));;

let cface bb = length(faces bb);;

let std_face_of_size bb r= 
  let f = (std_faces bb) in
  let z = enumerate f in 
    fst(split (filter (fun (_,y) -> (length(y)=r)) z));;


(* ampl data string of branch n bound *)

let unsplit d f = function
  | (x::xs) ->  fold_left (fun s t -> s^d^(f t)) (f x) xs
  | [] -> "";;

(* XXD *)

let ampl_string_of_bb outs bd = 
  let list_of xs = unsplit " " string_of_int xs in
  let edart_raw  = 
    map triples (faces bd) in
  let edart =
    let edata_row (i,x) = (sprintf "(*,*,*,%d) " i) ^ (unsplit ", " list_of x) in
      unsplit "\n" edata_row (enumerate edart_raw) in 
  Printf.fprintf outs
  "
param hypermapID := %s;
param CVERTEX := %d;
param CFACE := %d;

set ITRIANGLE := %s;
set IQUAD := %s;
set IPENT := %s;
set IHEX := %s;

set EDART := 
%s
;

set SUPER8 := %s;
set FLAT := %s;
set APIECE := %s;
set BIG5APEX := %s;
set BIG4APEX := %s;
set BIGTRI := %s;
set SMALLTRI := %s;
set HIGHVERTEX := %s;
set LOWVERTEX := %s;
" 
    (* hypermapid *) bd.hypermapid 
    (* CVERTEX *) (cvertex bd)
    (* CFACE *)   (cface bd)
    (* ITRIANGLE *) (list_of (std_face_of_size bd 3)) 
    (* IQUAD *) (list_of (std_face_of_size bd 4) )
    (* IPENT *) (list_of (std_face_of_size bd 5)) 
    (* IHEX *) (list_of (std_face_of_size bd 6))
    (* EDART *) (edart)
    (* SUPER8 *)  (list_of bd.super8)
    (* FLAT *) ""  (* these final fields are zero in basic lps *)
    (* APIECE *) ""
    (* BIG5APEX *) ""
    (* BIG4APEX *) ""
    (* BIGTRI *) ""
    (* SMALLTRI *) ""
    (* HIGHVERTEX *) ""
    (* LOWVERTEX *) "";;

let testps () =
  let file = "/tmp/out1.txt" in
  let outs = open_out file in
  let _ = ampl_string_of_bb outs (mk_bb pentstring) in
  let _ = close_out outs in
    Sys.command(sprintf "cat %s" file);;
 
(* running of branch in glpsol *)

let solve_branch bd = 
  let (ic,oc) = Unix.open_process(sprintf "glpsol -m %s -d /dev/stdin | grep '^ln' | sed 's/lnsum = //' "  model) in 
  let _ = ampl_string_of_bb oc bd in
  let _ = close_out oc in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
  let r = 
    if (length inp != 1) then raise (Failure ("Bad format:"^bd.hypermapid))
    else float_of_string (hd inp) in
  let _ = Sys.command(sprintf "echo %s: %3.3f\n" bd.hypermapid r) in 
    (bd,r);;

let filter_lp f bds = 
  let sol = map solve_branch bds in
  let (bds,_) = split (filter (fun (_,r) -> f r) sol) in
    bds;;

let feasible r = (r > 11.0);;

(*
let tame_hi = 
  let _ = Sys.command("date") in
  let h =  filter_lp feasible tame_bb
  let _ =  Sys.command("date") in
  h;;
(* 20:46-22:13 *)
save_stringarray archive_tame_hi (map (fun x -> x.string_rep) tame_hi);;
*)
  



(* split off a flat quarter *)
let split_face xs i =  (* {y1,y3} is the new diagonal *)
  let y1::y2::y3::ys = rotateL i xs in
  ([y1;y2;y3],(y3 :: ys @ [y1]));;
let asplit_pent xs i = (* y3 is the point of the A, {y1,y3}, {y3,y5} diags *)
  let y1::y2::y3::y4::[y5] = rotateL i xs in
  ([y1;y2;y3],[y1;y3;y5],[y5;y3;y4]);;


  
(* HEXAGON ANALYSIS *)
(* loop to run: *)
let hex_bb = filter (fun x -> length (std_face_of_size x 6) > 0) tame_bb;;
let hex_sol = map solve_branch hex_bb;;
let hex_hi = filter_feasible hex_sol hex_bb;;


(* branching *)
(* every hexagon either satisfies SHEX ineqs, or some dart in the hexagon is in SHEXDART *)

let solve_shex bd = 
   let r = { hypermapid = bd.hypermapid^ "00";
	       shex = (hd bd. ihex)::[];
	       faces = (faces bd);
	   } in
    solve_branch r;;



