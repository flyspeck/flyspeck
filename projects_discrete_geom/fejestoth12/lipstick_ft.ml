(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(*                                                                            *)
(* Linear Programs for Fejes Toth's Full Contact Conjecture *)
(* Chapter: Further Results                                                               *)
(* Author: Thomas C. Hales                                                    *)
(* Date: 2010-05-19                                                           *)
(* Guid: JKJNYAA (flypaper reference) *)
(* ========================================================================== *)

(*
needs new mktop on platforms that do not support dynamic loading of Str.

ocamlmktop unix.cma nums.cma str.cma -o ocampl
./ocampl

glpk needs to be installed, and glpsol needs to be found in the path.

*)

(* 
#directory "/Users/thomashales/Desktop/googlecode/flyspeck/glpk/";;
#use  "glpk_link.ml";;
*)

module Lipstick_ft = struct

open Glpk_link;;

(* external files. Edit for local system. *)
(* let datapath = "/Users/thomashales/Desktop/googlecode/flyspeck/graph_generator/output/";; *)
let datapath = "/tmp/";;
let glpkpath = "/Users/thomashales/Desktop/googlecode/flyspeck/glpk/";;

(* let archiveraw = datapath ^ "fejesToth.txt";; (*read only *) *)
let archiveraw = datapath ^ "graph_out.txt";; (*read only *)
let model = ref (glpkpath^ "fejesToth_contact/contact.mod");; (* read only *)
let tmpfile = "/tmp/graph.dat";;  (* temporary output *)
let dumpfile = "/tmp/graph.out";; (* temp output *)

(* type for holding the parameters for a linear program *)

type branchnbound = 
  { 
    hypermapid : string;
    mutable lpvalue : float option;
    std_faces : int list list;
    string_rep : string;
  };;

let mk_bb s = 
  let (h,face1) = convert_to_list s in
 {hypermapid= h;
  lpvalue = None;
  string_rep=s;
  std_faces = face1;
 };;

let std_faces bb = bb.std_faces;;

let rec rangeA a i j  = if (i >= j) then a
   else rangeA ((j-1)::a) i (j-1);;

let upt =   rangeA [] 0;;

let triples w = 
  let lw = List.length w in
  let r j = List.nth w (j mod lw)  in
  let triple i = 
      [r i; r (i+1); r(i+2)] in
    map triple (upt lw);;

let cvertex bb =
  1+ maxlist0 (List.flatten (std_faces bb));;

let cface bb = List.length(std_faces bb);;

let std_face_of_size bb r= 
  let f = std_faces bb in
  let z = enumerate f in 
    fst(List.split (filter (function _,y -> List.length y=r) z));;

let ampl_of_bb outs bb = 
  let fs = std_faces bb in
  let where3 = wheremod fs in
  let list_of = unsplit " " string_of_int in
  let edart_raw  = 
    map triples fs in
  let edart =
    let edata_row (i,x) = (sprintf "(*,*,*,%d) " i)^(unsplit ", " list_of x) in
      unsplit "\n" edata_row (enumerate edart_raw) in 
  let mk_dart xs = sprintf "%d %d" (hd xs) (where3 xs) in
  let mk_darts xs = (unsplit ", " mk_dart xs) in
  let p = sprintf in
  let j = join_lines [
    p"param hypermapID := %s;" bb.hypermapid ; 
    p"param CFACE := %d;\n" (cface bb);
    p"set ITRIANGLE := %s;" (list_of (std_face_of_size bb 3)) ;
    p"set IQUAD := %s;" (list_of (std_face_of_size bb 4) );
    p"set IPENT := %s;" (list_of (std_face_of_size bb 5)) ;
    p"set IHEX := %s;\n" (list_of (std_face_of_size bb 6));
    p"set EDART := \n%s;\n"  (edart);] in
    Printf.fprintf outs "%s" j;;  

(* read in the hypermap archive as java style strings *)

(*
let archive(raw) = strip_archive raw;;
*)

(* 2013-01, added arch as an explicit argument *)

let bbn arch i = mk_bb (List.nth arch i);;
let exec(arch) = 
  map (fun i -> solve_branch_f (!model) dumpfile "optival" ampl_of_bb (bbn arch i)) (0-- (List.length arch - 1));;

(* - : string list list =
  [([], ["opt.val = 0"]); (["PROBLEM HAS NO FEASIBLE SOLUTION"], []);
   ([], ["opt.val = 0"]); (["PROBLEM HAS NO FEASIBLE SOLUTION"], []);
   (["PROBLEM HAS NO FEASIBLE SOLUTION"], []);
   (["PROBLEM HAS NO FEASIBLE SOLUTION"], []);
   (["PROBLEM HAS NO FEASIBLE SOLUTION"], []); ([], ["opt.val = 0"])]

First two HCP, FCC. Next five infeasible.

Last is ruled out by hexagons perimeter argument in text.
   We are done!

rerun on Sept 25, 2012.
*)

end;;
