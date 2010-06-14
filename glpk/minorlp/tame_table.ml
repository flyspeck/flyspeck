(* ========================================================================== *)
(* FLYSPECK - GLPK                                              *)
(*                                                                            *)
(* Linear Programming, AMPL format (non-formal)    *)
(* Chapter:Tame Hypermap                          *)
(* Lemma: KCBLRQC (Tame Table B) *)
(* Author: Thomas C. Hales                                                    *)
(* Date: 2010-06-14                            *)
(* ========================================================================== *)

(*

The model considers nodes of type (p,q,0) and computes
the constants b(p,q).

It also computes the constant a(5,0,1).

*)


module Tame_table_b = struct

let rec cart b c = match b with
   [] -> []
  |b::bs -> (map (fun t -> (b,t)) c) @ cart bs c;;


open Str;;
open List;;
let sprintf = Printf.sprintf;;

let flyspeck_dir = 
  (try Sys.getenv "FLYSPECK_DIR" with Not_found -> Sys.getcwd());;
let glpk_dir = flyspeck_dir ^ "/../glpk";;

(* external files *)
let model = glpk_dir^ "/minorlp/tame_table.mod";;
let tmpfile = "/tmp/tame_table.dat";;
let dumpfile = "/tmp/tmp.out";;

let use_file_b s =
  (Toploop.use_file Format.std_formatter s) or 
  (Format.print_string("Error in included file "^s);Format.print_newline(); false);;

let linkfile = glpk_dir ^ "/glpk_link.ml";;

use_file_b linkfile;;

open Glpk_link;;

type node_type = 
  { 
    mutable lpvalue : float option;
    p : int;
    q : int;
    r : int;
  };;

(* the initial configuration always has a quarter at 0 *)
let mk_node p q r = 
 {
  p = p;
  q = q;
  r = r;
  lpvalue = None
 };;

let ampl_of_nt outs nt = 
  let pr = sprintf in
  let j = join_lines [
    pr"param p := %d;" nt.p;
    pr"param q := %d;" nt.q;
    pr"param r := %d;\n" nt.r;
   ] in
    Printf.fprintf outs "%s" j;;  

let test() = 
  let nt = mk_node 3 3 0 in
    display_ampl tmpfile ampl_of_nt nt;;

(* running of branch in glpsol *)

let set_some nt r = (* side effects *)
   if (length r = 1) then nt.lpvalue <- Some (float_of_string(hd r)) else ();;

let set_lpvalue nt = match nt.lpvalue with
  | None -> (set_some nt (solve_branch_f model dumpfile "tausum" ampl_of_nt nt))
  |  _ -> ();;


(* display_ampl tmpfile ampl_of_nt (mk_node 5 0 0);; *)

let f (p,q) = 
  (let nt = mk_node p q 0 in 
    set_lpvalue (nt); nt);;

let tame_table_b = 
  let target_ub = 1.542 in
  filter (fun t -> match t.lpvalue with
     None -> false
	  | Some r -> (r>0.0) & (r < target_ub)) (map f (cart  (0--10) (0--10)));;

let tame_table_a = 
   (let nt = mk_node 5 0 1 in
    set_lpvalue nt; nt);;

end;;
