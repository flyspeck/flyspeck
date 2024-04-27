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

flyspeck_needs "build/strictbuild.hl";;
flyspeck_needs "../formal_lp/glpk/glpk_link.ml";;
flyspeck_needs "../informal_code/graph_generator/graph_control.hl";;

module Tame_table = struct

  let squander_target = Graph_control.flyspeck_properties_2014.Graph_control.squander_target;;
  let table_weight_d = Graph_control.flyspeck_properties_2014.Graph_control.table_weight_d;;
  let table_weight_a = Graph_control.flyspeck_properties_2014.Graph_control.table_weight_a;;
  let table_weight_b = Graph_control.flyspeck_properties_2014.Graph_control.table_weight_b;;
  let node_card_max_at_exceptional_vertex = Graph_control.flyspeck_properties_2014.Graph_control.node_card_max_at_exceptional_vertex;;
  let fl x = float_of_int x /. 10000.0;;

type lptype = Lp_unset
	      | Lp_infeasible
	      | Lp_value of float;;

let string_of_lptype t = match t with
    | Lp_infeasible -> "infeasible"
    | Lp_unset -> "unset"
    | Lp_value u -> Printf.sprintf "%3.3f" u;;

let rec cart b c = match b with
   [] -> []
  |b::bs -> (map (fun t -> (b,t)) c) @ cart bs c;;


open Str;;
open List;;
open Glpk_link;;

let sprintf = Printf.sprintf;;

let glpk_dir = flyspeck_dir ^ "/../glpk";;

(* external files *)
let model = glpk_dir^ "/minorlp/tame_table.mod";;
let tmpfile = "/tmp/tame_table.dat";;
let dumpfile = "/tmp/tmp.out";;

type node_type = 
  { 
    mutable lpvalue : lptype;
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
  lpvalue = Lp_unset
 };;

let string_of_node t = 
  Printf.sprintf "%d %d %d %s" t.p t.q t.r (string_of_lptype t.lpvalue);;

let ampl_of_nt outs nt = 
  let pr = sprintf in
  let j = String.concat "\n" [
    pr"param p := %d;" nt.p;
    pr"param q := %d;" nt.q;
    pr"param r := %d;\n" nt.r;
   ] in
    Printf.fprintf outs "%s" j;;  

let test() = 
  let nt = mk_node 3 3 0 in
    display_ampl tmpfile ampl_of_nt nt;;

(* running of branch in glpsol *)

let set_lpvalue nt (f,r) = (* side effects *)
  let _ = 
    if (List.length f > 0) then nt.lpvalue <- Lp_infeasible
    else if (List.length r = 1) then nt.lpvalue <- Lp_value  (float_of_string(hd r))
    else nt.lpvalue <- Lp_unset in
    nt;;

let init_lpvalue nt = 
  let _ = match nt.lpvalue with
  | Lp_unset -> (set_lpvalue nt (solve_branch_f model dumpfile "tausum" ampl_of_nt nt))
  |  _ -> nt in
  let _ = report (string_of_node nt) in
    nt;;

(* display_ampl tmpfile ampl_of_nt (mk_node 5 0 0);; *)

let fpqr ((p,q),r) = init_lpvalue (mk_node p q r);;

let fpq (p,q) = fpqr((p,q),0);;

(* solve_branch_f model dumpfile "tausum" ampl_of_nt (mk_node 3 4 0);; *)

(* Each exception region contributes at least tame_table_d_5 *)

let filter1 = 
  let target_ub = 1.542 in
  let _ = target_ub > fl squander_target or failwith "bad target value" in
  let tame_table_d_5 = 0.4818 in
  let _ = tame_table_d_5 < fl (List.nth table_weight_d 5) or failwith "bad d5 value" in
  filter (fun t -> match t.lpvalue with
	      Lp_infeasible -> false
	    | Lp_unset -> true
	    | Lp_value s -> (s +. float_of_int t.r *. tame_table_d_5 < target_ub));;

let graph_control_unfound_b (t:node_type  ) = match (t.lpvalue) with
  | Lp_value u ->
      (try (
	 let eps = 1.0e-10 in (* allow roundoff error *)
	 let (_,_,v) = List.find (fun (a,b,_) -> (a=t.p && b = t.q)) table_weight_b in
	   u +. eps <= fl v
      )
      with Not_found -> true)
  | _ -> true
  ;;

let filter2 = filter graph_control_unfound_b;;

(* The case (p,q,r) = (0,2,0) is rejected by the convexity hypothesis. *)
(* The case (p,q,r) = (5,0,0) is done with calculation 4652969746 *)

let known_exceptions (t:node_type) = 
  not((t.p = 0 && t.q = 2 && t.r = 0) or (t.p = 5 && t.q = 0 && t.r = 0));;

let filter3 = filter known_exceptions;;

let tame_table_lp_data() = (map fpq (cart  (0--10) (0--10)));;

let tame_table_b_info() = 
  let n = filter3 (filter2 (filter1 (tame_table_lp_data()))) in
    if (List.length n = 0) then "All b table values have been accounted for in informal lp tests (ignoring 0,2,0 and 5,0,0)"
    else "Unaccounted for b values: \n" ^ String.concat "\n" (List.map string_of_node n);;

(* If r >= 4, then the dihedral sum is greater than 2 Pi *)

let pqrvalues  =
  let a =  (cart (cart  (0--6)  (0--6)) (1--3)) in
  filter (fun ((p,q),r) -> (p+q+r=6)) a;;
     

let badvalues_a (t:node_type) = match (t.lpvalue) with
  | Lp_value u ->
      (try (
	 let eps = 1.0e-10 in (* allow roundoff error *)
	 let (_,v) = List.find (fun (a,_) -> (a=t.p && (6-a) = t.q + t.r)) table_weight_a in
	   u +. eps <= fl v
      )
      with Not_found -> true)
  | _ -> true
  ;;

let filter_a = filter badvalues_a;;

let tame_table_a_info() = 
  let n =  filter_a (filter1 (map fpqr pqrvalues )) in
    if (List.length n = 0) then "All a table values have been accounted for in informal lp tests"
    else "Unaccounted for a values: \n" ^ String.concat "\n" (List.map string_of_node n);;

let execute() =
  let s = String.concat "\n" [tame_table_b_info();tame_table_a_info()] in
  let _ = report s in
    s;;



end;;
