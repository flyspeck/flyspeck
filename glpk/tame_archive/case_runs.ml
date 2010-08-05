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

(* Experimental section from here to the end of the file to eliminate final cases. *)
  let tmpfile = Filename.temp_file "display_ampl_" ".dat";;

Lpproc.archiveraw := "/Users/thomashales/Desktop/workspace/hanoi_workshop_files/tame_archive_svn1830.txt";;

let display_ampl =
   fun bb -> Glpk_link.display_ampl tmpfile Lpproc.ampl_of_bb bb;;

let display_lp bb = Glpk_link.display_lp 
  Lpproc.model tmpfile Lpproc.glpk_outfile Lpproc.ampl_of_bb bb ;;

let remake_model = 
  let bodyfile =  Filename.temp_file "body_" ".mod" in
  let m = Lpproc.model in
  fun () ->
    let _ = Lpproc.modelbody := bodyfile in
    let _ = Parse_ineq.output_string bodyfile (Parse_ineq.lpstring()) in    
    let _ = Sys.chdir(tame_dir) in
      Sys.command("cp head.mod "^m^"; cat "^bodyfile^" >> "^
                     m^"; cat tail.mod >> "^m);;

remake_model();;

let clone bb = modify_bb bb false [] [];;


let unset_edge bb = 
  let f = rotation (faces bb) in
  let g x = map (fun t -> [nth t 0; nth t 1]) x in
  sort (<) (nub(subtract (g f) (g bb.d_edge_200_225 @ g bb.d_edge_225_252)));;

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
  map resolve_with_hints r;;

let hard i = List.nth hard_bb i;;
(* map mk_gif hard_bb;; *)

(* restart Aug 2, 2010 *)


(* this eliminates case 11 *)
let b34970074286() = allpass_hint 500 [hard 11];;

(* this eliminates case 10, about 5000 linear programs *)

let b75641658977() = allpass_hint 2500 [hard 10];;

(*
  let b1 = allpass_hint 500 [hard 10] in
  let b2 = allpass_hint 500 b1 in
  let b3 = allpass_hint 500 b2 in
  let b4 = allpass_hint 500 b3 in
  let b5 = allpass_hint 500 b4 in
    b5;;
*)

(* this eliminates hard 9 88089363170 *)

let b88089363170() = allpass_hint 1000 [hard 9];;

let b86506100695() = allpass_hint 2000 [hard 8];;

let b242652038506() =  allpass_hint 10 [hard 7];;

let b179189825656() = allpass_hint 50 [hard 6];;

(* missing 5 *)

let b39599353438() = allpass_hint 10 [hard 4];;

let b65974205892() = allpass_hint 30 [hard 3];;

let b50803004532() = allpass_hint 500 [hard 2];;

let b223336279535() = allpass_hint_include_flat 20000 [hard 1];;

let b161847242261() = allpass_hint 5000 [hard 0];;  (* runs to 3583 *)


end;;
