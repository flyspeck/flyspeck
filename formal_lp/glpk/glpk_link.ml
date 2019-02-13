open Native_strictbuild;;
load_begin();;

(* ========================================================================== *)
(* FLYSPECK - BOOK FORMALIZATION                                              *)
(*                                                                            *)
(* Linear Programming Link                                                                  *)
(* Author: Thomas C. Hales                                                    *)
(* Date: 2010-05-19                                                           *)
(* ========================================================================== *)

(* 
This file contains material that does not depend on the details of the LP.
  list processing functions,
  IO operations,
  glpk function calls.
*)

(* module Glpk_link  = struct *)

(*

needs new mktop on platforms that do not support dynamic loading of Str.

ocamlmktop unix.cma nums.cma str.cma -o ocampl
./ocampl

glpk needs to be installed, and glpsol needs to be found in the path.

needs lib.ml from HOL Light and flyspeck_lib.hl from Flyspeck.
*)


open Str;;
open List;;
let sprintf = Printf.sprintf;;

let (nextc,resetc) = 
  let counter = ref 0 in
  ((fun () ->
    counter:= !counter + 1;
    !counter),(fun () -> (counter :=0)));;


(* list operations *)
let maxlist0 xs = fold_right max xs 0;; (* NB: value is always at least 0 *)

let get_values key xs = 
  map snd (find_all (function k,_ -> (k=key)) xs);;

(*
let rec sort cmp lis =  (* from HOL Light lib.ml *)
  match lis with
    [] -> []
  | piv::rest ->
      let r,l = partition (cmp piv) rest in
      (sort cmp l) @ (piv::(sort cmp r));;
*)

let sort = Lib.sort;;

let (--) = Lib.(--);;

(*
let rec (--) = fun m n -> if m > n then [] else m::((m + 1) -- n);; (* from HOL Light lib.ml *)
*)

let up i = 0 -- (i-1);;

let rec rotateL i xs = 
  if i=0 then xs 
  else match xs with
    | x::xss -> rotateL ((i-1) mod length xs) (xss @ [x])
    | [] -> [];;

let rotateR i = rotateL (-i);;

let rotation xs = 
  let maxsz = maxlist0 (map length xs) in
  flatten (map (fun i -> map (rotateL i) xs) (up maxsz));;


(* 
   zip from Harrison's lib.ml. 
   List.combine causes a stack overflow :
   let tt = up 30000 in combine tt tt;;
   Stack overflow during evaluation (looping recursion?).

let rec zip l1 l2 =
  match (l1,l2) with
        ([],[]) -> []
      | (h1::t1,h2::t2) -> (h1,h2)::(zip t1 t2)
      | _ -> failwith "zip";;
*)

let zip = Lib.zip;;

let enumerate xs = zip (up (length xs)) xs;;

let whereis i xs = 
  let (p,_) = find (function _,j -> j=i) (enumerate xs) in
    p;;

let wheremod xs x = 
  let ys = rotation xs in 
   (whereis x ys) mod (length xs);;

(* example *)
wheremod [[0;1;2];[3;4;5];[7;8;9]] [8;9;7];;  (* 2 *)


let unsplit = Flyspeck_lib.unsplit;;

let nub = Flyspeck_lib.nub;;

let join_lines = Flyspeck_lib.join_lines;;

(*
let rec nub = function
  | [] -> []
  | x::xs -> x::filter ((!=) x) (nub xs);;

let unsplit d f = function
  | (x::xs) ->  fold_left (fun s t -> s^d^(f t)) (f x) xs
  | [] -> "";;

let join_lines  = unsplit "\n" (fun x-> x);;
*)


(* read and write *)

(*
let load_and_close_channel do_close ic = 
  let rec lf ichan a = 
    try
      lf ic (Pervasives.input_line ic::a)
    with End_of_file -> a in
    let rs = lf ic [] in
      if do_close then Pervasives.close_in ic else ();
      rev rs;;

let load_file filename = 
  let ic = Pervasives.open_in filename in load_and_close_channel true ic;;

*)

let load_and_close_channel = Flyspeck_lib.load_and_close_channel;;

let load_file = Flyspeck_lib.load_file;;

let save_stringarray filename xs = 
  let oc = open_out filename in
    for i=0 to length xs -1
    do
      Pervasives.output_string oc (nth xs i ^ "\n");
      done;
    close_out oc;;

let strip_archive filename =  (* strip // comments, blank lines, quotation marks etc. *)
  let (ic,oc) = Unix.open_process(sprintf "cat %s | grep -v '=' | grep -v 'list' | grep -v '^//' | grep -v '^$' | grep '^[^a-z/-]' | sed 's/\"[,;]*//g' | sed 's/_//g' " filename) in
  let s = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
    s;;

(* example of java style string from hypermap generator. *)
let pentstring = "13_150834109178 18 3 0 1 2 3 3 2 7 3 3 0 2 4 5 4 0 3 4 6 1 0 4 3 7 2 8 3 8 2 1 4 8 1 6 9 3 9 6 10 3 10 6 4 3 10 4 5 4 5 3 7 11 3 10 5 11 3 11 7 12 3 12 7 8 3 12 8 9 3 9 10 11 3 11 12 9 ";;

(* conversion to list.  e.g. convert_to_list pentstring *)

let convert_to_list3  = 
  let split_sp=  Str.split (Str.regexp " +") in
  let strip_ = Str.global_replace (Str.regexp "_") "" in
  let rec movelist n (x,a) = 
    if n=0 then (x,a) else match x with y::ys -> movelist (n-1) (ys, y::a) in
  let getone (x,a) = match x with
    | [] -> ([],a)
    | y::ys -> let (u,v) = movelist y (ys,[]) in (u,v::a) in 
  let rec getall (x,a) =
    if (x=[]) then (x,a) else getall (getone (x,a)) in
  fun s ->
    let h::ss = (split_sp (strip_ s)) in
    let _::ns = map int_of_string ss in
    let (_,a) = getall (ns,[]) in
    (h,s,rev (map rev a));;

let convert_to_list = (fun (h,_,ls) -> (h,ls)) o convert_to_list3;;

(*
let convert_to_list  = 
  let split_sp=  Str.split (regexp " +") in
  let strip_ = global_replace (regexp "_") "" in
  let rec movelist n (x,a) = 
    if n=0 then (x,a) else match x with y::ys -> movelist (n-1) (ys, y::a) in
  let getone (x,a) = match x with
    | [] -> ([],a)
    | y::ys -> let (u,v) = movelist y (ys,[]) in (u,v::a) in 
  let rec getall (x,a) =
    if (x=[]) then (x,a) else getall (getone (x,a)) in
  fun s ->
    let h::ss = (split_sp (strip_ s)) in
    let _::ns = map int_of_string ss in
    let (_,a) = getall (ns,[]) in
     (h,rev (map rev a));;
*)

(* Linear programming *)

let display_ampl ampl_datafile ampl_of_bb bb = (* for debugging *)
  let outs = open_out ampl_datafile in
  let _ = ampl_of_bb outs bb in
  let _ = close_out outs in
    Sys.command(sprintf "cat %s" ampl_datafile);;

(* model should name the optimal value "optival" *)

let solve_counter=ref 0;;

let solve com model glpk_outfile varname ampl_of_bb bb = 
  let (ic,oc) = Unix.open_process(com) in 
  let _ = ampl_of_bb oc bb in
  let _ = close_out oc in
  let _ = (solve_counter := !solve_counter + 1) in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
  (* test for no feasible solution.  There are two different messages. *) 
(*  let _ = Sys.command("cat "^ glpk_outfile) in (* debug *) *) 
  let com2 = sprintf "grep \"PROBLEM HAS NO.*FEASIBLE SOLUTION\" %s" glpk_outfile in
  let (ic,oc)  =Unix.open_process(com2) in
  let inp2 = load_and_close_channel false ic in
  let _ = Unix.close_process(ic,oc) in
    (inp2,inp);;

let solve_branch_f model glpk_outfile varname ampl_of_bb bb = 
  let com = sprintf "glpsol -m %s -d /dev/stdin | tee %s | grep '^%s' | sed 's/.val//' | sed 's/%s = //' "  model glpk_outfile varname varname in 
  solve com model glpk_outfile varname ampl_of_bb bb;;

let solve_dual_f model glpk_outfile varname ampl_of_bb bb = 
  let com = sprintf "glpsol -m %s -d /dev/stdin --simplex --exact --dual -w /tmp/dual.out --output /tmp/output.out | tee %s | grep '^%s' | sed 's/.val//' | sed 's/%s = //' "  model glpk_outfile varname varname in 
  solve com model glpk_outfile varname ampl_of_bb bb;;

let display_lp model ampl_datafile glpk_outfile ampl_of_bb bb = 
  let oc = open_out ampl_datafile in
  let _ = ampl_of_bb oc bb in
  let _ = close_out oc in
  let com = sprintf "glpsol -m %s -d %s | tee %s" model ampl_datafile glpk_outfile in
  let _ = Sys.command(com) in 
    ();;

let cpx_branch model cpxfile ampl_of_bb bb = (* debug *)
  let com = sprintf "glpsol -m %s --wcpxlp %s -d /dev/stdin | grep '^opti' | sed 's/optival = //' "  model cpxfile in 
  let (ic,oc) = Unix.open_process(com) in 
  let _ = ampl_of_bb oc bb in
  let _ = close_out oc in
  let _ = load_and_close_channel false ic in
  let _ = Unix.close_process (ic,oc) in
  sprintf "cplex file created of lp: %s" cpxfile;;

(* for debugging: reading optimal variables values from the glpk_outfile *)

let get_dumpvar glpk_outfile s = (* read variables from glpk_outfile *)
  let com = sprintf "grep '%s' %s | sed 's/^.*= //'  " s glpk_outfile in
  let (ic,oc) = Unix.open_process(com) in
  let _ = close_out oc in
  let inp = load_and_close_channel false ic in
  let _ = Unix.close_process(ic,oc) in
  inp;;
(* get_dumpvar "yn.0.*=";; *) 

(* end;; *)

load_end __FILE__;;