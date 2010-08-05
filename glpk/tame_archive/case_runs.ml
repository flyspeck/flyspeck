(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(*                                                                            *)
(* Chapter: Linear Programs                                         *)
(* Author: Thomas C. Hales                                                    *)
(* Date: 2010-08-01                                                           *)
(* ========================================================================== *)

(* Linear Programs for the hard cases.  Individual case runs *)

flyspeck_needs "nonlinear/parse_ineq.hl";;
flyspeck_needs "nonlinear/temp_ineq.hl";;
flyspeck_needs "../glpk/tame_archive/lpproc.ml";;
flyspeck_needs "../glpk/tame_archive/hard_lp.ml";;

module Lp_case_analysis = struct

  open Glpk_link;;
  open Lpproc;;
  open Hard_lp;;
  open List;;
  open Sphere_math;;
  open Temp_ineq;;  (* needs to be open for referencing in external files to work properly!  *)
  open Tame_scaffolding;;

Lpproc.archiveraw := "/Users/thomashales/Desktop/workspace/hanoi_workshop_files/tame_archive_svn1830.txt";;

remake_model();;

let hardid = Lpproc.hardid;;

let hard_string_rep = 
   List.find_all (fun s -> mem (fst (Glpk_link.convert_to_list s)) hardid) 
   (Glpk_link.strip_archive (!Lpproc.archiveraw));;

let resolve_with_hints t = 
  let u = resolve t in 
  let _ = add_hints_force u in
    u;;

let resolve_with_hints_include_flat t = 
  let u = resolve t in 
  let _ = add_hints_force_include_flat u in
    u;;

let hard_bb =  
  let r = map mk_bb hard_string_rep in
  map resolve_with_hints_include_flat r;;


let execute() = 
  let _ = resetc() in
  map (fun t-> allpass_hint_include_flat 50000 [t]) hard_bb;;



let hard i = List.nth hard_bb i;;


end;;
