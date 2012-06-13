(* ========================================================================== *)
(* FLYSPECK - GLPK                                                            *)
(*                                                                            *)
(* Linear Programming, AMPL format (non-formal)                               *)
(* Chapter: Packing                                                           *)
(* Lemma: OXLZLEZ                                                             *)
(* Author: Thomas C. Hales                                                    *)
(* Date: 2009-09-22, rechecked 2010-06-03, 2012-06-08                         *)
(* ========================================================================== *)

(*

This file generates the informal linear programming part of the cluster inequality (OXLZLEZ).
These linear programs reduce the 3 and 4 blade cases to a single case:
   4 blades with 3 quarters and 1 4-cell of weight 0.5.
This final case is handled separately.



needs new mktop on platforms that do not support dynamic loading of Str.

ocamlmktop unix.cma str.cma -o ocampl
./ocampl

*)


flyspeck_needs "../glpk/glpk_link.ml";;

module Oxlzlez_informal = struct

open Str;;
open List;;
open Glpk_link;;

let sprintf = Printf.sprintf;;

let glpk_dir = flyspeck_dir ^ "/../glpk";;

(* external files *)
let model = glpk_dir^ "/minorlp/OXLZLEZ.mod";;
let tmpfile = "/tmp/OXLZLEZ_informal.dat";;
let dumpfile = "/tmp/OXLZLEZ_informal.out";;

type lptype = Lp_unset
	      | Lp_infeasible
	      | Lp_value of (((string * int list) * string * float) list)*float;;


let string_of_lptype t = match t with
    | Lp_infeasible -> "infeasible"
    | Lp_unset -> "unset"
    | Lp_value (_,u) -> Printf.sprintf "%3.3f" u;;


(* fields of bladerunner are documented in OXLZLEZ.mod.
   See CBLADE,SBLADE,NONSBLADE,QU,QX,QY,QXD,NONQXD,NEGQU,POSQU,
   HALFWT,FULLWT,SHORTY4,LONGY4
*)

type bladerunner = 
  { 
    mutable lpvalue : lptype;
    mutable history : string;
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

let backup = ref [];;

(* the initial configuration always has a quarter at 0 *)
let mk_br n = 
  let br = 
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
  lpvalue = Lp_unset;
  history="";
 } in
  let _ = (backup := br ::!backup) in
  br;;

let modify_br h br fields  = 
  let _ = (br.history <- h) in
  let add s vs = nub((get_values s fields) @ vs) in
  let br' = {
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
lpvalue = Lp_unset;
history = "";
} in
  let _ = (backup:= br':: !backup) in
  br'
;;

(*
Example: move 1 into halfwt
let brx = modify_br "" (mk_br 4)   ["halfwt",1];;
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
  let br =  modify_br "test" br  ["qu",1;"qu",2;"negqu",3] in
    display_ampl tmpfile ampl_of_br br;;

(* manipulations of lpvalue field that don't involve glpsol *)

let notdone r = (r < 0.0);;

let select_notdone f brs = (* selects unset and those satisfying f *)
    let fil ro = match ro.lpvalue with
	Lp_unset -> true
      | Lp_infeasible -> false
      | Lp_value (_,r) -> f r in 
      filter fil brs;;

let is_unset br = match br.lpvalue with
    Lp_unset -> true
  | _ -> false;;

let calc_min brs = fold_right
  (fun br x -> match br.lpvalue with
     |Lp_value (_,y) -> min x y
     |_ -> x
  ) brs 10.0;;

let find_min brs = 
  let t = calc_min brs in
  (* let r = Lp_value (t) in *)
    find (fun br -> 
      match br.lpvalue with
	|  Lp_value (_,y) -> (y=t)
	| _ -> false) brs;;


(* 
branching. 
We fail on the branching if the branch has been made already,
 or if the necessary prior branches have not been followed.
*)

let branch h br ss i  = 
   map (fun s -> modify_br h br [s,i]) ss;;

let branch_sblade i br  =
  let _ = not(mem i br.sblade or mem i br.nonsblade) or failwith "sblade" in
    branch "sblade" br ["sblade"; "nonsblade"] i;;

let branch_qxd i br  = 
  let _ = mem i br.qx or   failwith "qxd1" in
  let _ = not(mem i br.qxd or mem i br.nonqxd) or failwith "qxd2" in
      branch "qxd" br ["qxd";"nonqxd"] i;;

let branch_negqu i br  =
  let _ =  mem i br.qu or failwith "negqu1" in
  let _ =  not(mem i br.negqu or mem i br.posqu) or failwith "negqu2" in
     branch "negqu" br ["negqu";"posqu"] i;;

let branch_wt i br  = 
  let _ = mem i br.qx or failwith "wt-qx" in
  let _ = (mem i br.sblade && mem (next br i) br.sblade) or failwith "wt-blade" in
  let _ = not(mem i br.halfwt or mem i br.fullwt) or failwith "wt-set" in
      branch "wt" br ["halfwt";"fullwt"] i;;

let branch_y4 i br = 
  let _ = mem i br.qy or failwith "y4-qy" in
  let _ = (mem i br.sblade && mem (next br i) br.sblade) or failwith "y4-blade" in
    branch "y4" br ["shorty4";"longy4"] i;;

let branch_qu i br  = 
  let j = next br i in
  let _ = not(mem i br.qu or mem i br.qx or mem i br.qy) or failwith "qu-set" in
  let _ = not(mem i br.nonsblade or mem j br.nonsblade) or failwith "qu-blade" in
   modify_br "qus" br ["sblade",i;"sblade",j;"qu",i] :: branch "qu" br ["qx";"qy"] i;;

(* (* example *)
let br = mk_br 3;;
let br1 = List.nth (branch_qu 1 br) 1;;
let br2 = List.nth (branch_sblade 2 br1) 0;;
branch_wt 1 br2;;
*)

(* Link in glpsol linear programming package *) 

let load_dual() =
  let outputf = Flyspeck_lib.load_file "/tmp/output.out" in
  let output_split = map (Str.split (Str.regexp " +")) outputf in
  let output_active = filter 
    (fun xs ->
       if (List.length xs <3) then false else
	 let n = List.nth xs 0 in
	 let t = List.nth xs 2 in
	 let v = hd (List.rev xs) in
	   (can int_of_string n && t.[0]='N') && not(v="eps")) output_split in
  let output_format = map
    (fun xs -> 
       (strip_id (List.nth xs 1),List.nth xs 2,
	float_of_string (hd (List.rev xs)))) 
    output_active in
    output_format;;

let set_lpvalue nt (dualdata,(f,r)) = (* side effects *)
  let _ = 
    if (List.length f > 0) then nt.lpvalue <- Lp_infeasible
    else if (List.length r = 1) 
    then 
      nt.lpvalue <- Lp_value  (dualdata, float_of_string(hd r))
    else 
      nt.lpvalue <- Lp_unset in
    nt;;

let solve_and_set_lp br = 
  let _ = match br.lpvalue with
    | Lp_unset -> (* generate dual data as soon as lp is solved *)
      let fr =  (Glpk_link.solve_dual_f model dumpfile "gammasum" ampl_of_br br) in
      let dualdata = load_dual() in
      (set_lpvalue br (dualdata,fr))
    |  _ -> br in
  let _ = report (string_of_lptype br.lpvalue) in
  br;;


(* control flow *)

let ex0 brancher i brs = (flatten (map (brancher i) brs));;

let ex brancher i brs = 
  let brs' = ex0 brancher i brs in
(*  let _ = map set_lpvalue brs' in *)
   select_notdone notdone (map solve_and_set_lp brs');;

let top brancher i (br::rest) = (ex brancher i [br]) @ rest;;

let bury (x::xs) = xs @ [x];;

(* case of 3 blades: *)
let blade3() = 
  let br = mk_br 3 in
  let br1 = ex branch_qu 2 (branch_qu 1 br) in
  let br2 = ex branch_negqu 0 br1 in
  let br3 = ex branch_qxd 2 br2 in
  let br4 = ex branch_qxd 1 br3 in
   br4;;

(* case of 4 blades *)
let blade4() = 
  let cr = mk_br 4 in 
  let cr1 = ex branch_qu 3 (ex0 branch_qu 2 (branch_qu 1 cr)) in 
  let cr2 = bury (top branch_wt 3 cr1) in 
  let cr2' = top branch_y4 3 cr2 in 
  let cr3 = bury (top branch_wt 2 cr2') in 
  let cr4 = top branch_sblade 3 cr3 in 
  let cr5' = top branch_sblade 3 cr4 in 
  let cr5 = top branch_y4 2 cr5' in
  let cr6 = top branch_sblade 3 cr5 in 
  let cr7 = bury(top branch_wt 1 cr6) in 
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


let execute() = 
  let b3 = blade3() in
  let b3_info = if (List.length b3 = 0) then "blade 3 passes" else failwith "blade 3 fails in OXLZLEZ" in
  let b4 = blade4() in
  let t0 = nub (map test_structure (b4)) in
  let b4_info =  if (t0=[true]) then "blade 4 passes (ignoring cases with 4 blades, 3 quarters, 1 4-cell with wt 0.5)"
  else failwith "blade 4 fails in OXLZLEZ" in
  let s =     join_lines [b3_info;b4_info] in
  let _ = report s in
    s;;

end;;
