(* ========================================================================== *)
(* FLYSPECK - GLPK                                              *)
(*                                                                            *)
(* Linear Programming, AMPL format (non-formal)    *)
(* Chapter: Packing                                                     *)
(* Lemma: OXLZLEZ *)
(* Author: Thomas C. Hales                                                    *)
(* Date: 2009-09-22, rechecked 2010-06-03                                   *)
(* ========================================================================== *)

(*

This file generates the linear programming part of the cluster inequality (OXLZLEZ).
These linear programs reduce the 3 and 4 blade cases to a single case:
   4 blades with 3 quarters and 1 4-cell of weight 0.5.
This final case is handled separately.

needs new mktop on platforms that do not support dynamic loading of Str.

ocamlmktop unix.cma str.cma -o ocampl
./ocampl

*)


module Cluster = struct

open Str;;
open List;;
let sprintf = Printf.sprintf;;

let flyspeck_dir = 
  (try Sys.getenv "FLYSPECK_DIR" with Not_found -> Sys.getcwd());;
let glpk_dir = flyspeck_dir ^ "/../glpk";;

(* external files *)
let model = "/tmp/OXLZLEZ.mod";;
let tmpfile = "/tmp/cluster.dat";;
let dumpfile = "/tmp/tmp.out";;

let use_file_b s =
  (Toploop.use_file Format.std_formatter s) or 
  (Format.print_string("Error in included file "^s);Format.print_newline(); false);;

let linkfile = glpk_dir ^ "/glpk_link.ml";;

use_file_b linkfile;;

open Glpk_link;;

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
    shorty4: int list;
    longy4:int list;
  };;

let next br i = (i+1) mod br.cblade;;

(* the initial configuration always has a quarter at 0 *)
let mk_br n = 
 {cblade = n;
  sblade = [0;1];   (* quarter at 0.  "raw" blades: face 0 goes with raw blades 0 & 1. *)
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
  shorty4=[];
  longy4=[];
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
shorty4 = add "shorty4" br.shorty4;  (* y4 <= 2.1 *)
longy4 = add "longy4" br.longy4;   (* y4 >= 2.1 *)
lpvalue = None;
}
;;

(*
Example: move 1 into halfwt
let brx = modify_br (mk_br 4)   ["halfwt",1];;
*) 

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
    mk "FULLWT" br.fullwt;
    mk "LONGY4" br.longy4;
    mk "SHORTY4" br.shorty4] in
    Printf.fprintf outs "%s" j;;  

let test() = 
  let br = mk_br 4 in
  let br =  modify_br br  ["qu",1;"qu",2;"negqu",3] in
    display_ampl tmpfile ampl_of_br br;;

(* running of branch in glpsol *)

let set_some br r = (* side effects *)
   if (length r = 1) then br.lpvalue <- Some (float_of_string(hd r)) else ();;

let set_lpvalue br = match br.lpvalue with
  | None -> (set_some br (solve_branch_f model dumpfile "gammasum" ampl_of_br br))
  |  _ -> ();;

(* selects None and those satisfying f *)

let select_notdone f brs = 
  let _ = map set_lpvalue brs in
    let fil ro = match ro.lpvalue with
	None -> true
      | Some r -> f r in 
      filter fil brs;;

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
We fail on the branching if the branch has been made already,
 or if the necessary prior branches have not been followed.
*)

let branch br ss i  = 
   map (fun s -> modify_br br [s,i]) ss;;

let branch_sblade i br  =
  let _ = not(mem i br.sblade or mem i br.nonsblade) or failwith "sblade" in
    branch br ["sblade"; "nonsblade"] i;;

let branch_qxd i br  = 
  let _ = mem i br.qx or   failwith "qxd1" in
  let _ = not(mem i br.qxd or mem i br.nonqxd) or failwith "qxd2" in
      branch br ["qxd";"nonqxd"] i;;

let branch_negqu i br  =
  let _ =  mem i br.qu or failwith "negqu1" in
  let _ =  not(mem i br.negqu or mem i br.posqu) or failwith "negqu2" in
     branch br ["negqu";"posqu"] i;;

let branch_wt i br  = 
  let _ = mem i br.qx or failwith "wt-qx" in
  let _ = (mem i br.sblade && mem (next br i) br.sblade) or failwith "wt-blade" in
  let _ = not(mem i br.halfwt or mem i br.fullwt) or failwith "wt-set" in
      branch br ["halfwt";"fullwt"] i;;

let branch_y4 i br = 
  let _ = mem i br.qy or failwith "y4-qy" in
  let _ = (mem i br.sblade && mem (next br i) br.sblade) or failwith "y4-blade" in
    branch br ["shorty4";"longy4"] i;;

let branch_qu i br  = 
  let j = next br i in
  let _ = not(mem i br.qu or mem i br.qx or mem i br.qy) or failwith "qu-set" in
  let _ = not(mem i br.nonsblade or mem j br.nonsblade) or failwith "qu-blade" in
   modify_br br ["sblade",i;"sblade",j;"qu",i] :: branch br ["qx";"qy"] i;;

(* (* example *)
let br = mk_br 3;;
let br1 = List.nth (branch_qu 1 br) 1;;
let br2 = List.nth (branch_sblade 2 br1) 0;;
branch_wt 1 br2;;
*)

(* control flow *)

let ex0 brancher i brs = (flatten (map (brancher i) brs));;

let ex brancher i brs = 
  let brs' = ex0 brancher i brs in
  let _ = map set_lpvalue brs' in
   select_notdone notdone brs';;

let top brancher i (br::rest) = (ex brancher i [br]) @ rest;;
let delay (x::xs) = xs @ [x];;

(* case of 3 blades: *)
let blade3 = 
  let br = mk_br 3 in
  let br1 = ex branch_qu 2 (branch_qu 1 br) in
  let br2 = ex branch_negqu 0 br1 in
  let br3 = ex branch_qxd 2 br2 in
  let br4 = ex branch_qxd 1 br3 in
   br4;;

(* case of 4 blades *)
let blade4 = 
  let cr = mk_br 4 in 
  let cr1 = ex branch_qu 3 (ex0 branch_qu 2 (branch_qu 1 cr)) in 
  let cr2 = delay (top branch_wt 3 cr1) in 
  let cr2' = top branch_y4 3 cr2 in 
  let cr3 = delay (top branch_wt 2 cr2') in 
  let cr4 = top branch_sblade 3 cr3 in 
  let cr5' = top branch_sblade 3 cr4 in 
  let cr5 = top branch_y4 2 cr5' in
  let cr6 = top branch_sblade 3 cr5 in 
  let cr7 = delay(top branch_wt 1 cr6) in 
  let cr8 = top branch_sblade 2 cr7 in 
  let cr9 = top branch_sblade 2 cr8 in 
  let cr10' = top branch_sblade 2 cr9 in 
  let cr10 = top branch_y4 1 cr10' in 
  let cr11 = top branch_sblade 2 cr10 in 
   cr11;;
(* three cases remain, all related by symmetry. 4 blades, 3 quarters, 1 4-cell with weight 0.5 *)

let test_structure br = 
  let _ = (sort (<) br.sblade = [0;1;2;3]) or failwith "sblade" in
  let _ = ((length br.qx = 1) && (br.qx = br.halfwt)) or failwith "weight" in
  let _ = (length br.qu = 3) or failwith "qu" in
   true;;

nub (map test_structure blade4);;

end;;
