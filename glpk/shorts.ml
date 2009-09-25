(*
Thomas C. Hales
Sept 22, 2009
Process short linear programs for the proof of the Kepler conjecture.
modified from lpproc.ml, much of the code is repeated or slightly modified.

needs new mktop on platforms that do not support dynamic loading of Str.

ocamlmktop unix.cma str.cma -o ocampl
./ocampl

*)

open Str;;
open List;;
let sprintf = Printf.sprintf;;

(* external files *)
let model = "shorts.mod";;
let tmpfile = "/tmp/shorts.dat";;

(* list operations *)
let maxlist0 xs = fold_right max xs 0;; (* NB: value is always at least 0 *)

let get_values key xs = 
  map snd (find_all (function k,_ -> (k=key)) xs);;

let upto = 
  let rec rangeA a i j  = if (i >= j) then a
   else rangeA ((j-1)::a) i (j-1)  in
  rangeA [] 0;;

let rec zip l1 l2 =
  match (l1,l2) with
        ([],[]) -> []
      | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
      | _ -> failwith "zip";;

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


type bladerunner = 
  { 
    mutable lpvalue : float option;
    cblade : int; (* number of blades *)
    sblade : int list;
    nonsblade : int list;
    qu: int list;
    qx : int list;
    qy : int list;
    qxd : int list;
    nonqxd : int list;
    negqu : int list;
    posqu : int list;
    halfwt : int list;
    fullwt : int list;
  };;

let next br i = (i+1) mod br.cblade;;

(* the initial configuration always has a quarter at 0 *)
let mk_br n = 
 {cblade = n;
  sblade = [0;1]; 
  nonsblade = [];
  qu = [0];
  qx = [];
  qy = [];
  qxd = [];
  nonqxd = [];
  negqu = [];
  posqu = [];
  halfwt = [];
  fullwt = [];
  lpvalue = None;
 };;

let modify_br br fields  = 
  let add s vs = nub((get_values s fields) @ vs) in
{
cblade = br.cblade;
sblade = add "sblade" br.sblade;
nonsblade = add "nonsblade" br.nonsblade;
qu = add "qu" br.qu;
qx = add "qx" br.qx;
qy = add "qy" br.qy;
qxd = add "qxd" br.qxd;
nonqxd = add "nonqxd" br.nonqxd;
negqu = add "negqu" br.negqu;
posqu = add "posqu" br.posqu;
halfwt = add "halfwt" br. halfwt;
fullwt = add "fullwt" br.fullwt;
lpvalue = None;
}
;;




(*
Example: move 1 into halfwt
let brx = modify_br (mk_br 4)   ["halfwt",1];;
*) 

(* ampl data string of branch n bound *)

let unsplit d f = function
  | (x::xs) ->  fold_left (fun s t -> s^d^(f t)) (f x) xs
  | [] -> "";;

let join_lines  = unsplit "\n" (fun x-> x);;

let ampl_of_br outs br = 
  let list_of = unsplit " " string_of_int in
  let p = sprintf in
  let mk s f = p"set %s := %s;" s (list_of f) in
  let j = join_lines [
    p"param CBLADE := %d;" br.cblade ;
    mk "SBLADERAW" br.sblade;
    mk "NONSBLADERAW" br.nonsblade;
    mk "QU" br.qu;
    mk "QX" br.qx;
    mk "QY" br.qy;
    mk "QXD" br.qxd;
    mk "NONQXD" br.nonqxd;
    mk "NEGQU" br.negqu;
    mk "POSQU" br.posqu;
    mk "HALFWT" br. halfwt;
    mk "FULLWT" br.fullwt] in
    Printf.fprintf outs "%s" j;;  

(* 
Example:
   ampl_of_br stdout brx;;
*)

let tampl br =
  let file = tmpfile in 
  let outs = open_out file in
  let _ = ampl_of_br outs br in
  let _ = close_out outs in
    Sys.command(sprintf "cat %s" file);;

(* Example:
tampl brx;;
*)

let test() = 
  let br = mk_br 4 in
  let br =  modify_br br  ["qu",1;"qu",2;"negqu",3] in
    tampl br;;

(* running of branch in glpsol *)

let set_some br r = (* side effects *)
   if (length r = 1) then br.lpvalue <- Some (float_of_string(hd r)) else ();;


let solve_branch br = (* side effects, lpvalue mutable *)
  let com = sprintf "glpsol -m %s -d /dev/stdin | grep '^gamma' | sed 's/gammasum = //' "  model in 
  let (ic,oc) = Unix.open_process(com) in 
  let _ = ampl_of_br oc br in
  let _ = close_out oc in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
  let _ = set_some br inp in
  let r = match br.lpvalue with
    | None -> -1.0
    | Some r -> r in
  let _ = Sys.command(sprintf "echo %s: %3.3f\n" "case_undisclosed" r) in 
    br;;

let display_lp br = (* for debugging *)
  let oc = open_out tmpfile in
  let _ = ampl_of_br oc br in
  let _ = close_out oc in
  let com = sprintf "glpsol -m %s -d %s" model tmpfile in
  let _ = Sys.command(com) in 
    ();;

let solve br = match br.lpvalue with
  | None -> solve_branch br
  | Some _ -> br;;

(* selects None and those satisfying f *)

let select_notdone f brs = 
  let sol = map solve brs in
    let fil ro = match ro.lpvalue with
	None -> true
      | Some r -> f r in 
      filter fil sol;;

let notdone r = (r < 0.0);; (* if infeasible, returns 0. if infeasible then done *)

let is_none br = match br.lpvalue with
    None -> true
  | Some _ -> false;;

let calc_min brs = fold_right
  (fun br x -> match br.lpvalue with
     |None -> x
     |Some y -> min x y) brs 10.0;;

let find_min brs = 
  let r = Some (calc_min brs) in
    find (fun br -> r = br.lpvalue) brs;;

(* 
branching.
*)

let branch br ss i rest = 
  flatten (map (fun s -> modify_br br [s,i] :: rest) ss);;

(*
We fail on the branching if the branch has been made already,
 or if the necessary prior branches have not been followed.
*)

let branchsblade br ss i rest = 
  let m x = modify_br br x :: rest in
  let j = next br i in 
  if (mem i br.nonsblade or mem j br.nonsblade) then failwith "bsb"
    else flatten (map (fun s -> m( if snd s then 
      ["sblade",i;"sblade",j; fst s,i] else [fst s,i])) ss);;


(* particular branching *)

let branch_sblade i br  =
  if (mem i br.sblade or mem i br.nonsblade) then failwith "sblade"
    else branch br ["sblade"; "nonsblade"] i [];;

let branch_qu i br  = 
  if (mem i br.qu or mem i br.qx or mem i br.qy) then failwith "qu"
    else if (mem i br.nonsblade or mem (next br i) br.nonsblade) then failwith "qu2"
    else branchsblade br ["qu",true;"qx",false;"qy",false] i [];;

let branch_qxd i br  = 
  if not(mem i br.qx) then failwith "qxd1"
    else if (mem i br.qxd or mem i br.nonqxd) then failwith "qxd2"
      else branch br ["qxd";"nonqxd"] i [];;

let branch_negqu i br  =
  if not(mem i br.qu) then failwith "negqu1"
    else if (mem i br.negqu or mem i br.posqu) then failwith "negqu2"
      else branch br ["negqu";"posqu"] i [];;

let branch_wt i br  = 
  if not(mem i br.qx) then failwith "wt1"
    else if (mem i br.halfwt or mem i br.fullwt) then failwith "wt2"
      else if (not(mem i br.sblade && mem (next br i) br.sblade)) then failwith "wt3"
      else branch br ["halfwt";"fullwt"] i [];;

let ex0 ch i brs = (flatten (map (ch i) brs));;
let ex ch i brs = select_notdone notdone (map solve (ex0 ch i brs));;

let top ch i (br::rest) = (ex ch i [br]) @ rest;;
let delay (x::xs) = xs @ [x];;

(* case of 3 blades: *)
let br = mk_br 3;;
let br1 = ex branch_qu 2 (branch_qu 1 br);;
let br2 = ex branch_negqu 0 br1;;
let br3 = ex branch_qxd 2 br2;;
let br4 = ex branch_qxd 1 br3;;


(* case of 4 blades *)
let cr = mk_br 4;;
let cr1 = ex branch_qu 3 (ex0 branch_qu 2 (branch_qu 1 cr));;
let cr2 = delay (top branch_wt 3 cr1);;
let cr3 = delay (top branch_wt 2 cr2);;
let cr4 = top branch_sblade 3 cr3;;
let cr5 = top branch_sblade 3 cr4;;
let cr6 = top branch_sblade 3 cr5;;
let cr7 = delay(top branch_wt 1 cr6);;
let cr8 = top branch_sblade 2 cr7;;
let cr9 = top branch_sblade 2 cr8;;
let cr10 = top branch_sblade 2 cr9;;
let cr11 = top branch_sblade 2 cr10;;
(* three cases remain, all related by symmetry *)
let cr12 = nth cr11 0;;  (* one of them *)
