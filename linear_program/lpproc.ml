(*
Thomas C. Hales
June 25, 2009
Process linear programs for the proof of the Kepler conjecture.

needs to use ocamlstr (new top level with Str preloaded) on platforms that do not support dynamic loading of Str.
*)
open Str;;
open List;;


let rec range i j a = if (i >= j) then a
   else range i (j-1) ((j-1)::a);;

(* example of java style string from graph generator. *)
let pentstring = "13_150834109178 18 3 0 1 2 3 3 2 7 3 3 0 2 4 5 4 0 3 4 6 1 0 4 3 7 2 8 3 8 2 1 4 8 1 6 9 3 9 6 10 3 10 6 4 3 10 4 5 4 5 3 7 11 3 10 5 11 3 11 7 12 3 12 7 8 3 12 8 9 3 9 10 11 3 11 12 9 ";;

(* conversion to list data *)
let convert_to_list = 
  let split_sp=  split (regexp " ") in
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
    let a = map (map ((+) 1)) a in
    (h,rev (map rev a));;

type basic_data = 
  {mutable graphid : string;
  mutable cvertex :int;
  mutable  cface :int;
  mutable  itriangle: int list;
  mutable  iquad: int list;
  mutable  ipent:  int list;
  mutable  ihex: int list;
  mutable  edart:  int list list list};;

let mk_basic_data s = 
  let (h,faces) = convert_to_list s in
  let lf = length(faces) in
  let z = combine (range 1 (lf+1) []) faces in
  let len r= fst(split (filter (fun (_,y) -> (length(y)==r)) z)) in
  let triple w i = 
    let r j = nth w (j mod length w)  in
      [r i; r (i+1); r(i+2)] in
  let triples w = map (triple w) (range 0 (length w) []) in
 {graphid= h;
  cvertex= fold_right max (flatten faces) 0;
  cface= length(faces);
  itriangle=len 3;
  iquad=len 4;
  ipent=len 5;
  ihex=len 6;
  edart=map triples faces;
 };;

let list_of xs = fold_right (fun x y -> (Printf.sprintf " %d" x)^y) xs "";;

let print_basic_data bd = 
  Printf.sprintf 
  "
param graphID := %s;
param CVERTEX := %d;
param CFACE := %d

set ITRIANGLE := %s;
set IQUAD := %s;
set IPENT := %s;
set IHEX := %s;

set EDART;;
" 
bd.graphid bd.cvertex bd.cface (list_of bd.itriangle) (list_of bd.iquad) (list_of bd.ipent) (list_of bd.ihex);;
