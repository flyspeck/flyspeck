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

module Lipstick_ft = struct

#directory "/Users/thomashales/Desktop/googlecode/flyspeck/glpk/";;
#use  "glpk_link.ml";;
open Glpk_link;;

(* external files. Edit for local system. *)
let datapath = "/Users/thomashales/Desktop/googlecode/flyspeck/graph_generator/output/";;
let glpkpath = "/Users/thomashales/Desktop/googlecode/flyspeck/glpk/";;

let archiveraw = datapath ^ "fejesToth.txt";; (*read only *)
let model = glpkpath^ "fejesToth_contact/contact.mod";; (* read only *)
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

let triples w = 
  let r j = nth w (j mod length w)  in
  let triple i = 
      [r i; r (i+1); r(i+2)] in
    map triple (upto (length w));;

let cvertex bb =
  1+ maxlist0 (flatten (std_faces bb));;

let cface bb = length(std_faces bb);;

let std_face_of_size bb r= 
  let f = std_faces bb in
  let z = enumerate f in 
    fst(split (filter (function _,y -> length y=r) z));;

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

let archive = strip_archive archiveraw;;
let bbn i = mk_bb (List.nth archive i);;
map (fun i -> solve_branch_f model dumpfile ampl_of_bb (bbn i)) [0;1;2;3;4;5;6;7];;
(* - : string list list =
[["-10"]; ["-10"]; ["0"]; ["0"]; ["0"]; ["0"]; ["-9.25508116531845"];
 ["-10"]] *)
(* interpretation:
    The first one HCP is feasible
   The second FCC is feasible
   The next four are infeasible
   The next is feasible but Girard's formula for solid angles cannot hold.
   The last is feasible but flypaper. gives a geometric argument to rule it out.

   We are done!
*)

end;;
