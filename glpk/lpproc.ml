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
let tamehi = "/tmp/tamehi.txt";; (* output *)

(* list operations *)
let range = 
  let rec rangeA a i j  = if (i >= j) then a
   else rangeA ((j-1)::a) i (j-1)  in
  rangeA [];;
let rec rotateL i xs = 
  if (i<=0) then xs 
  else match xs with
    | x::xss -> rotateL (i-1) (xss @ [x])
    | [] -> [];;
let rec rotateTo xs i j = 
  match xs with
    | [] -> []
    | x::xss -> if (x==i) then xs else
	if(j<0) then raise (Failure "element not found") 
	else rotateTo (rotateL 1 xs) i (j-1);;
(* canonical order of cyclic list with distinct entries *)
let canon xs =
  let m = fold_right min xs (hd xs) in (rotateTo xs m (length xs));;


(* example of java style string from hypermap generator. *)
let pentstring = "13_150834109178 18 3 0 1 2 3 3 2 7 3 3 0 2 4 5 4 0 3 4 6 1 0 4 3 7 2 8 3 8 2 1 4 8 1 6 9 3 9 6 10 3 10 6 4 3 10 4 5 4 5 3 7 11 3 10 5 11 3 11 7 12 3 12 7 8 3 12 8 9 3 9 10 11 3 11 12 9 ";;

(* read in the tame hypermap archive as java style strings *)
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

let strip_archive () =
  let (ic,oc) = Unix.open_process(sprintf "tail -n +70 %s | grep -v '//' | grep -v '^$' | sed 's/\"[,]*//g' | sed 's/_//g' " archiveraw) in
  let s = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
    s;;

let tame = strip_archive();;

(* conversion to list data.  e.g. convert_to_list pentstring *)
let convert_to_list = 
  let split_sp=  Str.split (regexp " ") in
  let strip_ = global_replace (regexp "_") "" in
  let rec movelist n (x,a) = 
    if n==0 then (x,a) else match x with y::ys -> movelist (n-1) (ys, y::a) in
  let getone (x,a) = match x with
    | [] -> ([],a)
    | y::ys -> let (u,v) = movelist y (ys,[]) in (u,v::a) in 
  let rec getall (x,a) =
    if (x=[]) then (x,a) else getall (getone (x,a)) in
  fun s ->
    let h::ss = (split_sp (strip_ s)) in
    let _::ns = map int_of_string ss in
    let (_,a) = getall (ns,[]) in
    (h,rev (map rev a));;

(* conversion to basic data.  e.g. mk_basic_data pentstring  *)

type basic_data = 
  { 
    hypermapid : string;
    faces: int list list;
    super8: int list;
  };;

let mk_basic_data s = 
  let (h,face1) = convert_to_list s in
 {hypermapid= h;
  faces = face1;
  super8=[];
 };;
let tame_data = map mk_basic_data tame;; 


(* functions on basic data *)

let triples w = 
  let triple w i = 
    let r j = nth w (j mod length w)  in
      [r i; r (i+1); r(i+2)] in
    map (triple w) (range 0 (length w));;

let basic_edart data = 
    map triples data.faces;;

let cvertex data =
  1+ fold_right max (flatten data.faces) 0;;

let cface data = length(data.faces);;

let lenface data r= 
  let f = data.faces in
  let z = combine (range 0 (length f)) f in
    fst(split (filter (fun (_,y) -> (length(y)==r)) z));;


(* printing of basic data *)

let unsplit d f = function
  | (x::xs) ->  fold_left (fun s t -> s^d^(f t)) (f x) xs
  | [] -> "";;

let print_basic_data outs bd = 
  let list_of xs = unsplit " " string_of_int xs in
  let edataf =
    let edata_row (i,x) = (sprintf "(*,*,*,%d) " i) ^ (unsplit ", " list_of x) in
      fun x -> unsplit "\n" edata_row (combine (range 0 (length x)) x) in
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
    (* ITRIANGLE *) (list_of (lenface bd 3)) 
    (* IQUAD *) (list_of (lenface bd 4) )
    (* IPENT *) (list_of (lenface bd 5)) 
    (* IHEX *) (list_of (lenface bd 6))
    (* EDART *) (edataf (basic_edart bd))
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
  let _ = print_basic_data outs (mk_basic_data pentstring) in
  let _ = close_out outs in
    Sys.command(sprintf "cat %s" file);;
 
(* running of basic data in glpsol *)

let solve_basic bd = 
  let (ic,oc) = Unix.open_process(sprintf "glpsol -m %s -d /dev/stdin | grep '^ln' | sed 's/lnsum = //' "  model) in 
  let _ = print_basic_data oc bd in
  let _ = close_out oc in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
  let (h,r) = 
    if (length inp != 1) then raise (Failure ("Bad format:"^bd.hypermapid))
    else (bd.hypermapid, float_of_string (hd inp)) in
  let _ = Sys.command(sprintf "echo %s: %3.3f\n" h r) in 
    (h,r);;

(*
let filter_feasible_old  sols datas =
   let (h,_) = split (filter (fun (_,(_,r)) ->  (r > 12.0)) (combine (range 0 (length sols)) sols)) in 
  map (nth datas) h;;
*)

(* zip from Harrison's lib.ml. List.combine causes a stack overflow for mysterious reasons. *)
let rec zip l1 l2 =
  match (l1,l2) with
        ([],[]) -> []
      | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
      | _ -> failwith "zip";;

let filter_feasible f bs cs = 
  let combs =	zip cs (zip bs (range 0 (length bs))) in
  let (h,_) = split (filter (fun (_,(r,_)) -> f r) combs) in
    h;;


let tame_hi_compute() = 
  let tame_sol = map solve_basic tame_data in
  filter_feasible (fun (_,r) -> (r > 11.0)) tame_sol tame;;

(*
let tame_hi = tame_hi_compute();;
Stack overflow during evaluation (looping recursion?).
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
let hex_data = filter (fun x -> length (lenface x 6) > 0) tame_data;;
let hex_sol = map solve_basic hex_data;;
let hex_hi = filter_feasible hex_sol hex_data;;


(* branching *)
(* every hexagon either satisfies SHEX ineqs, or some dart in the hexagon is in SHEXDART *)

let solve_shex bd = 
   let r = { hypermapid = bd.hypermapid^ "00";
	       shex = (hd bd. ihex)::[];
	       faces = bd.faces;
	   } in
    solve_basic r;;



