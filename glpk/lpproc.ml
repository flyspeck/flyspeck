(*
Thomas C. Hales
June 25, 2009
Process linear programs for the proof of the Kepler conjecture.

needs to use ocamlstr (new top level with Str preloaded) on platforms that do not support dynamic loading of Str.
*)
open Str;;
open List;;
let sprintf = Printf.sprintf;;

(* example of java style string from graph generator. *)
let pentstring = "13_150834109178 18 3 0 1 2 3 3 2 7 3 3 0 2 4 5 4 0 3 4 6 1 0 4 3 7 2 8 3 8 2 1 4 8 1 6 9 3 9 6 10 3 10 6 4 3 10 4 5 4 5 3 7 11 3 10 5 11 3 11 7 12 3 12 7 8 3 12 8 9 3 9 10 11 3 11 12 9 ";;

(* read in the tame graph archive as java style strings *)
let archiveraw = "/tmp/tame_graph.txt";;
let archive = "/tmp/tame_stripped.txt";;
let strip_text () =
  Sys.command(sprintf "tail -n +70 %s | grep -v '//' | grep -v '^$' | sed 's/\"[,]*//g' | sed 's/_//g' > %s" archiveraw archive);;
let load_file filename = 
  let ic = open_in filename in
  let rec lf ichan a = 
    try
      lf ic ((input_line ic)::a)
    with End_of_file -> a in
    let rs = lf ic [] in
      close_in ic; rs;;
let read_archive() = load_file archive;;
(* let tame = rev (read_archive());; *)

let range = 
  let rec rangeA a i j  = if (i >= j) then a
   else rangeA ((j-1)::a) i (j-1)  in
  rangeA [];;


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
    let a = map (map ((+) 1)) a in
    (h,rev (map rev a));;

(* conversion to basic data.  e.g. mk_basic_data pentstring  *)

type basic_data = 
  {mutable graphid : string;
  mutable cvertex :int;
  mutable  cface :int;
  mutable  itriangle: int list;
  mutable  iquad: int list;
  mutable  ipent:  int list;
  mutable  ihex: int list;
  mutable  shex: int list;
  mutable  edart:  int list list list};;

let mk_basic_data s = 
  let (h,faces) = convert_to_list s in
  let lf = length(faces) in
  let z = combine (range 1 (lf+1)) faces in
  let len r= fst(split (filter (fun (_,y) -> (length(y)==r)) z)) in
  let triple w i = 
    let r j = nth w (j mod length w)  in
      [r i; r (i+1); r(i+2)] in
  let triples w = map (triple w) (range 0 (length w)) in
 {graphid= h;
  cvertex= fold_right max (flatten faces) 0;
  cface= length(faces);
  itriangle=len 3;
  iquad=len 4;
  ipent=len 5;
  ihex=len 6;
  shex=[];
  edart=map triples faces;
 };;
(* let tame_data = map mk_basic_data tame;; *)

(* printing of basic data *)

let unsplit d f = function
  | (x::xs) ->  fold_left (fun s t -> s^d^(f t)) (f x) xs
  | [] -> "";;

let print_basic_data outs bd = 
  let list_of xs = unsplit " " string_of_int xs in
  let edata =
    let edata_row (i,x) = (sprintf "(*,*,*,%d) " i) ^ (unsplit ", " list_of x) in
      fun x -> unsplit "\n" edata_row (combine (range 1 (length x + 1)) x) in
  let out = open_out outs in
  Printf.fprintf out
  "
param graphID := %s;
param CVERTEX := %d;
param CFACE := %d;

set ITRIANGLE := %s;
set IQUAD := %s;
set IPENT := %s;
set IHEX := %s;

set EDART := 
%s
;

# branch and bound on hexagons
set SHEX := %s;
" 
(* graphid *) bd.graphid 
(* CVERTEX *) bd.cvertex 
(* CFACE *)   bd.cface 
(* ITRIANGLE *) (list_of bd.itriangle) 
(* IQUAD *) (list_of bd.iquad) 
(* IPENT *) (list_of bd.ipent) 
(* IHEX *) (list_of bd.ihex) 
(* EDART *) (edata bd.edart)
(* SHEX *)  (list_of bd.shex)
  ; close_out out;;

(* running of basic data *)
let model = "/tmp/graph0.mod";;
let data = "/tmp/graph.dat";;
let silent _ = ();;
let solve_basic bd =
  print_basic_data data bd;
  let fileIO = sprintf "/tmp/out/sol%s.txt" bd.graphid in
    silent (Sys.command(sprintf "echo %s; glpsol -m %s -d %s | grep 'lnsum =' | sed 's/lnsum = //' > %s"  bd.graphid model data fileIO));
    let inp = load_file fileIO in
    if (length inp != 1) then raise (Failure ("Bad format:"^bd.graphid))
      else (bd.graphid, float_of_string (hd inp));;
  
(* HEXAGON ANALYSIS *)
(* loop to run: *)
let hex_data = filter (fun x -> length (x.ihex) > 0) tame_data;;
let hex_sol = map solve_basic hex_data;;
let hex_hi = 
  let (h,_) = split (filter (fun (_,(_,r)) -> (r > 11.0)) (combine (range 0 (length hex_sol)) hex_sol)) in 
  map (nth hex_data) h;;

(* branching *)
(* every hexagon either satisfies SHEX ineqs, or some dart in the hexagon is in SHEXDART *)

let solve_shex bd = 
   let r = { graphid = bd.graphid^ "00";
	       cvertex = bd.cvertex;
	       cface = bd.cface;
	       itriangle = bd.itriangle;
	       iquad = bd.iquad;
	       ipent = bd.ipent;
	       ihex = bd.ihex;
	       shex = (hd bd. ihex)::[];
	       edart = bd.edart;
	   } in
    solve_basic r;;



